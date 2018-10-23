// Parses the development applications at the South Australian City of Port Lincoln web site and
// places them in a database.
//
// Michael Bone
// 18th October 2018

"use strict";

import * as cheerio from "cheerio";
import * as request from "request-promise-native";
import * as sqlite3 from "sqlite3";
import * as urlparser from "url";
import * as moment from "moment";
import * as pdfjs from "pdfjs-dist";
import * as didyoumean from "didyoumean2";

sqlite3.verbose();

const DevelopmentApplicationsUrl = "https://www.portlincoln.sa.gov.au/DevelopmentRegister";
const CommentUrl = "mailto:plcc@plcc.sa.gov.au";

declare const process: any;

// Sets up an sqlite database.

async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text)");
            resolve(database);
        });
    });
}

// Inserts a row in the database if it does not already exist.

async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or ignore into [data] values (?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate
        ], function(error, row) {
            if (error) {
                console.error(error);
                reject(error);
            } else {
                if (this.changes > 0)
                    console.log(`    Inserted: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" into the database.`);
                else
                    console.log(`    Skipped: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" because it was already present in the database.`);
                sqlStatement.finalize();  // releases any locks
                resolve(row);
            }
        });
    });
}

// A bounding rectangle.

interface Rectangle {
    x: number,
    y: number,
    width: number,
    height: number
}

// An element (consisting of text and a bounding rectangle) in a PDF document.

interface Element extends Rectangle {
    text: string,
    confidence: number
}

// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.  Take care to avoid extremely tall elements (because these may otherwise
// be considered as part of all rows and effectively force the return value of this function to
// the same value, regardless of the value of startElement).

function getRowTop(elements: Element[], startElement: Element) {
    let top = startElement.y;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y)  // check for overlap
            if (getVerticalOverlapPercentage(startElement, element) > 50)  // avoids extremely tall elements
                if (element.y < top)
                    top = element.y;
    return top;
}

// Constructs a rectangle based on the intersection of the two specified rectangles.

function intersect(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}

// Calculates the square of the Euclidean distance between two elements.

function calculateDistance(element1: Element, element2: Element) {
    let point1 = { x: element1.x + element1.width, y: element1.y + element1.height / 2 };
    let point2 = { x: element2.x, y: element2.y + element2.height / 2 };
    if (point2.x < point1.x - element1.width / 5)  // arbitrary overlap factor of 20% (ie. ignore elements that overlap too much in the horizontal direction)
        return Number.MAX_VALUE;
    return (point2.x - point1.x) * (point2.x - point1.x) + (point2.y - point1.y) * (point2.y - point1.y);
}

// Determines whether there is vertical overlap between two elements.

function isVerticalOverlap(element1: Element, element2: Element) {
    return element2.y < element1.y + element1.height && element2.y + element2.height > element1.y;
}

// Gets the percentage of vertical overlap between two elements (0 means no overlap and 100 means
// 100% overlap; and, for example, 20 means that 20% of the second element overlaps somewhere
// with the first element).

function getVerticalOverlapPercentage(element1: Element, element2: Element) {
    let y1 = Math.max(element1.y, element2.y);
    let y2 = Math.min(element1.y + element1.height, element2.y + element2.height);
    return (y2 < y1) ? 0 : (((y2 - y1) * 100) / element2.height);
}

// Gets the element immediately to the right of the specified element (but ignores elements that
// appear after a large horizontal gap).

function getRightElement(elements: Element[], element: Element) {
    let closestElement: Element = { text: undefined, confidence: 0, x: Number.MAX_VALUE, y: Number.MAX_VALUE, width: 0, height: 0 };
    for (let rightElement of elements)
        if (isVerticalOverlap(element, rightElement) &&  // ensure that there is at least some vertical overlap
            getVerticalOverlapPercentage(element, rightElement) > 50 &&  // avoid extremely tall elements (ensure at least 50% overlap)
            (rightElement.x > element.x + element.width) &&  // ensure the element actually is to the right
            (rightElement.x - (element.x + element.width) < 30) &&  // avoid elements that appear after a large gap (arbitrarily ensure less than a 30 pixel gap horizontally)
            calculateDistance(element, rightElement) < calculateDistance(element, closestElement))  // check if closer than any element encountered so far
            closestElement = rightElement;
    return (closestElement.text === undefined) ? undefined : closestElement;
}

// Gets the text to the right in a rectangle, where the rectangle is delineated by the positions
// in which the three specified strings of (case sensitive) text are found.

function getRightText(elements: Element[], topLeftText: string, rightText: string, bottomText: string) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.

    let topLeftElement = elements.find(element => element.text.trim() == topLeftText);
    let rightElement = (rightText === undefined) ? undefined : elements.find(element => element.text.trim() == rightText);
    let bottomElement = (bottomText === undefined) ? undefined: elements.find(element => element.text.trim() == bottomText);
    if (topLeftElement === undefined)
        return undefined;

    let x = topLeftElement.x + topLeftElement.width;
    let y = topLeftElement.y;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);

    let bounds: Rectangle = { x: x, y: y, width: width, height: height };

    // Gather together all elements that are at least 50% within the bounding rectangle.

    let intersectingElements: Element[] = []
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }

    // Sort the elements by Y co-ordinate and then by X co-ordinate.

    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);

    // Join the elements into a single string.

    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Gets the text downwards in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.

function getDownText(elements: Element[], topText: string, rightText: string, bottomText: string) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.

    let topElement = elements.find(element => element.text.trim() == topText);
    let rightElement = (rightText === undefined) ? undefined : elements.find(element => element.text.trim() == rightText);
    let bottomElement = (bottomText === undefined) ? undefined: elements.find(element => element.text.trim() == bottomText);
    if (topElement === undefined)
        return undefined;

    let x = topElement.x;
    let y = topElement.y + topElement.height;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);

    let bounds: Rectangle = { x: x, y: y, width: width, height: height };

    // Gather together all elements that are at least 50% within the bounding rectangle.

    let intersectingElements: Element[] = []
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }

    // Sort the elements by Y co-ordinate and then by X co-ordinate.

    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);

    // Join the elements into a single string.

    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Parses the details from the elements associated with a single development application.

function parseApplicationElements(elements: Element[], startElement: Element, informationUrl: string) {
    // Get the application number.

    let applicationNumber = getRightText(elements, "Application No", "Application Date", "Applicants Name");
    if (applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    console.log(`    Found \"${applicationNumber}\".`);

    // Get the received date.

    let receivedDateText = getRightText(elements, "Application received", "Planning Approval", "Building Application");
    let receivedDate: moment.Moment = undefined;
    if (receivedDateText !== undefined)
        receivedDate = moment(receivedDateText.trim(), "D/MM/YYYY", true);

    // Get the address.

    let address = "";

    let houseNumber = getRightText(elements, "Property House No", "Planning Conditions", "Lot");
    if (houseNumber !== undefined && houseNumber !== "0")
        address += houseNumber;

    let streetName = getRightText(elements, "Property Street", "Planning Conditions", "Property Suburb");
    if (streetName === undefined || streetName === "" || streetName === "0") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because an address was not found or parsed (there is no street name).  Elements: ${elementSummary}`);
        return undefined;
    }
    address += ((address === "") ? "" : " ") + streetName;

    let suburbName = getRightText(elements, "Property Suburb", "Planning Conditions", "Title");
    if (suburbName === undefined || suburbName === "" || suburbName === "0")
        suburbName = "PORT LINCOLN SA 5606";
    else
        suburbName += " SA 5606";

    address += ((address === "") ? "" : ", ") + suburbName.replace(/ STAGE ONE/g, "").replace(/LINCOLN COVEüLINCO /g, "LINCOLN COVE ").replace(/PORT LINCOLNüPORT LINCOLN /g, "PORT LINCOLN ");
    address = address.replace(/ü/g, " ").trim();

    // Get the description.

    let description = getDownText(elements, "Development Description", "Relevant Authority", "Private Certifier Name");

    // Construct the resulting application information.
    
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description === "") ? "NO DESCRIPTION PROVIDED" : description),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : ""
    };
}

// Finds the start element of each development application on the current PDF page (there are
// typically two development applications on a single page and each development application
// typically begins with the text "Application No").

function findStartElements(elements: Element[]) {
    // Examine all the elements on the page that being with "A" or "a".
    
    let startElements: Element[] = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith("a"))) {
        // Extract up to 15 elements to the right of the element that has text starting with the
        // letter "a" (and so may be the start of the "Application No" text).  Join together the
        // elements to the right in an attempt to find the best match to "Application No".

        let rightElement = element;
        let rightElements: Element[] = [];
        let matches = [];

        do {
            rightElements.push(rightElement);
        
            let text = rightElements.map(element => element.text).join("").replace(/\s/g, "").toLowerCase();
            if (text.length >= 15)  // stop once the text is too long
                break;
            if (text.length >= 10) {  // ignore until the text is close to long enough
                if (text === "applicationno")
                    matches.push({ element: rightElement, threshold: 0 });
                else if (didyoumean(text, [ "ApplicationNo" ], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 1, trimSpace: true }) !== null)
                    matches.push({ element: rightElement, threshold: 1 });
                else if (didyoumean(text, [ "ApplicationNo" ], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true }) !== null)
                    matches.push({ element: rightElement, threshold: 2 });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 15);

        // Chose the best match (if any matches were found).

        if (matches.length > 0) {
            let bestMatch = matches.reduce((previous, current) =>
                (previous === undefined ||
                previous.threshold < current.threshold ||
                (previous.threshold === current.threshold && Math.abs(previous.text.length - "ApplicationNo".length) <= Math.abs(current.text.length - "ApplicationNo".length)) ? current : previous), undefined);
            startElements.push(bestMatch.element);
        }
    }

    // Ensure the start elements are sorted in the order that they appear on the page.

    let yComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
    startElements.sort(yComparer);
    return startElements;
}

// Parses a PDF document.

async function parsePdf(url: string) {
    let developmentApplications = [];

    // Read the PDF.

    let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);

    // Parse the PDF.  Each page has the details of multiple applications.

    let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
    for (let pageIndex = 0; pageIndex < pdf.numPages; pageIndex++) {
        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);

        // Construct a text element for each item from the parsed PDF information.

        let textContent = await page.getTextContent();
        let viewport = await page.getViewport(1.0);
        let elements: Element[] = textContent.items.map(item => {
            let transform = pdfjs.Util.transform(viewport.transform, item.transform);

            // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
            // exaggerated).  The problem seems to be that the height value is too large in some
            // PDFs.  Provide an alternative, more accurate height value by using a calculation
            // based on the transform matrix.

            let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);
            return { text: item.str, x: transform[4], y: transform[5], width: item.width, height: workaroundHeight };
        });

        // Sort the elements by Y co-ordinate and then by X co-ordinate.

        let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
        elements.sort(elementComparer);

        // Group the elements into sections based on where the "Application No" text starts (and
        // any other element the "Application No" elements line up with horizontally with a margin
        // of error equal to about half the height of the "Application No" text).

        let applicationElementGroups = [];
        let startElements = findStartElements(elements);
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).  Allow some leeway vertically (add some extra height).
            
            let startElement = startElements[index];
            let raisedStartElement: Element = {
                text: startElement.text,
                confidence: startElement.confidence,
                x: startElement.x,
                y: startElement.y - startElement.height / 2,  // leeway
                width: startElement.width,
                height: startElement.height };
            let rowTop = getRowTop(elements, raisedStartElement);
            let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;

            // Extract all elements between the two rows.

            applicationElementGroups.push({ startElement: startElements[index], elements: elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop) });
        }

        // Parse the development application from each group of elements (ie. a section of the
        // current page of the PDF document).  If the same application number is encountered a
        // second time add a suffix to the application number so it is unique (and so will be
        // inserted into the database later instead of being ignored).

        for (let applicationElementGroup of applicationElementGroups) {
            let developmentApplication = parseApplicationElements(applicationElementGroup.elements, applicationElementGroup.startElement, url);
            if (developmentApplication !== undefined) {
                let suffix = 0;
                let applicationNumber = developmentApplication.applicationNumber;
                while (developmentApplications.some(otherDevelopmentApplication => otherDevelopmentApplication.applicationNumber === developmentApplication.applicationNumber))
                    developmentApplication.applicationNumber = `${applicationNumber} (${++suffix})`;  // add a unique suffix
                developmentApplications.push(developmentApplication);
            }
        }
    }

    return developmentApplications;
}

// Gets a random integer in the specified range: [minimum, maximum).

function getRandom(minimum: number, maximum: number) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}

// Pauses for the specified number of milliseconds.

function sleep(milliseconds: number) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}

// Parses the development applications.

async function main() {
    // Ensure that the database exists.

    let database = await initializeDatabase();

    // Retrieve the page that contains the links to the PDFs.

    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);

    let body = await request({ url: DevelopmentApplicationsUrl, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);
    
    let pdfUrls: string[] = [];
    for (let element of $("td.uContentListDesc a[href$='.pdf']").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl);
        if (!pdfUrls.some(url => url === pdfUrl.href))  // avoid duplicates
            pdfUrls.push(pdfUrl.href);
    }

    if (pdfUrls.length === 0) {
        console.log("No PDF URLs were found on the page.");
        return;
    }

    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).

    let selectedPdfUrls: string[] = [];
    selectedPdfUrls.push(pdfUrls.shift());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(1, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();

    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl);
        console.log(`Parsed ${developmentApplications.length} development application(s) from document: ${pdfUrl}`);
        console.log(`Inserting development applications into the database.`);
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}

main().then(() => console.log("Complete.")).catch(error => console.error(error));
