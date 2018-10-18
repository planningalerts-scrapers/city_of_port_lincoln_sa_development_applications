// Parses the development applications at the South Australian City of Port Lincoln web site and
// places them in a database.
//
// Michael Bone
// 18th October 2018

"use strict";

import * as fs from "fs";
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

// All valid street and suburb names.

let SuburbNames = null;
let StreetSuffixes = null;
let StreetNames = null;

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

// Calculates the area of a rectangle.

function getArea(rectangle: Rectangle) {
    return rectangle.width * rectangle.height;
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

// Gets the text to the right of the specified startElement up to the left hand side of the
// specified middleElement (adjusted left by 20% of the width of the middleElement as a safety
// precaution).  Only elements that overlap 50% or more in the vertical direction with the
// specified startElement are considered (ie. elements on the same "row" and not too tall).

function getRightRowText(elements: Element[], startElement: Element, middleElement: Element) {
    let rowElements = elements.filter(element =>
        element.x > startElement.x + startElement.width &&
        element.x < middleElement.x - 0.2 * middleElement.width &&
        getVerticalOverlapPercentage(element, startElement) > 50
    );

    // Sort and then join the elements into a single string.

    let xComparer = (a: Element, b: Element) => (a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0);
    rowElements.sort(xComparer);
    return rowElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Reads all the address information into global objects.

function readAddressInformation() {
    StreetNames = {}
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        if (StreetNames[streetName] === undefined)
            StreetNames[streetName] = [];
        StreetNames[streetName].push(suburbName);  // several suburbs may exist for the same street name
    }

    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.split(",");
        StreetSuffixes[streetSuffixTokens[0].trim().toLowerCase()] = streetSuffixTokens[1].trim();
    }

    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.split(",");
        let suburbName = suburbTokens[0].trim().toLowerCase();
        let suburbStateAndPostCode = suburbTokens[1].trim();
        SuburbNames[suburbName] = suburbStateAndPostCode;
    }
}

// Gets the elements on the line above (typically an address line).

function getAboveElements(elements: Element[], leftElement: Element, belowElement: Element, middleElement: Element) {
    // Find the elements above (at least a "line" above) the specified belowElement and to the
    // left of the middleElement.  These elements correspond to address elements (assumed to be on
    // one single line).

    let addressElements = elements.filter(element =>
        element.y < belowElement.y - belowElement.height &&
        element.x < middleElement.x - 0.2 * middleElement.width &&
        element.x > leftElement.x - leftElement.height);  // use height rather than width purposely (to avoid too much width)
        
    // Find the lowest address element (this is assumed to form part of the single line of the
    // address).  Note that middleElement.x is divided by two so that elements on the very right
    // hand side of the rectangle being searched will be ignored (these tend to be descriptions
    // that have been moved too far to the left, overlapping the rectangle in which the address
    // is expected to appear).

    let addressBottomElement = addressElements.reduce((previous, current) => ((current.x < middleElement.x / 2) && (previous === undefined || current.y > previous.y) ? current : previous), undefined);
    if (addressBottomElement === undefined)
        return [];

    // Obtain all elements on the same "line" as the lowest address element.

    addressElements = elements.filter(element =>
        element.y < belowElement.y - belowElement.height &&
        element.x < middleElement.x - 0.2 * middleElement.width &&
        element.x > leftElement.x - leftElement.height &&   // use height rather than width purposely (to avoid too much width)
        element.y >= addressBottomElement.y - Math.max(element.height, addressBottomElement.height));

    // Sort the address elements by Y co-ordinate and then by X co-ordinate (the Math.max
    // expressions exist to allow for the Y co-ordinates of elements to be not exactly aligned).

    let elementComparer = (a, b) => (a.y > b.y + Math.max(a.height, b.height)) ? 1 : ((a.y < b.y - Math.max(a.height, b.height)) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    addressElements.sort(elementComparer);

    // Remove any address elements that occur after a sizeable gap.  Any such elements are very
    // likely part of the description (not the address) because sometimes the description is
    // moved to the left, closer to the address.

    for (let index = 1; index < addressElements.length; index++) {
        if (addressElements[index].x - (addressElements[index - 1].x + addressElements[index - 1].width) > 50) {  // gap greater than 50 pixels
            if (addressElements[index - 1].confidence >= 60 && addressElements[index].confidence >= 60) {  // avoid random marks and the edge of the paper being recognised as text
                addressElements.length = index;  // remove the element and all following elements that appear after a large gap
                break;
            }
        }
    }

    return addressElements;
}

// Finds the element containing the "Assessment Number" text.  This is a good starting point from
// which to find other elements for the application (such as the address elements).

function getAssessmentNumberElement(elements: Element[], startElement: Element) {
    // Find the "Assessment Number" or "Asses Num" text (allowing for spelling errors).

    let assessmentNumberElement = elements.find(element =>
        element.y > startElement.y &&
        didyoumean(element.text, [ "Assessment Number", "Asses Num" ], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 3, trimSpace: true }) !== null);

    if (assessmentNumberElement !== undefined)
        return assessmentNumberElement;

    // Find any occurrences of the text "Assessment" or "Asses".

    let assessmentElements = elements.filter(
        element => element.y > startElement.y &&
        didyoumean(element.text, [ "Assessment", "Asses" ], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true }) !== null);

    // Check if any of the occurrences of "Assessment" are followed by "Number" or "Num".

    for (let assessmentElement of assessmentElements) {
        let assessmentRightElement = getRightElement(elements, assessmentElement);
        if (assessmentRightElement !== undefined && didyoumean(assessmentRightElement.text, [ "Number", "Num" ], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true }) !== null)
            return assessmentElement;
    }

    return undefined;
}

// Gets the element containining the received date.

function getReceivedDateElement(elements: Element[], startElement: Element, middleElement: Element) {
    // Search to the right of "Dev App No." for the lodged date (including some leeway up and
    // down a few "lines" from the "Dev App No." text because sometimes the lodged date is offset
    // vertically by a fair amount; in some cases offset up and in other cases offset down).

    let dateElements = elements.filter(element => element.x >= middleElement.x &&
        element.y + element.height > startElement.y - 4 * startElement.height &&
        element.y < startElement.y + 4 * startElement.height &&
        moment(element.text.trim(), "D/MM/YYYY", true).isValid());

    // Select the left most date (ie. favour the "lodged" date over the "final descision" date).

    let receivedDateElement = dateElements.reduce((previous, current) => ((previous === undefined || previous.x > current.x) ? current : previous), undefined);
    return receivedDateElement;
}

// Gets the description.

function getDescription(elements: Element[], startElement: Element, middleElement: Element, receivedDateElement: Element) {
    // Set the element which delineates the top of the description text.

    let descriptionTopElementY = (receivedDateElement === undefined) ? startElement.y : (receivedDateElement.y + receivedDateElement.height);

    // Set the element which delineates the bottom left of the description text.
    
    let descriptionBottomLeftElement = middleElement;
    
    // Extract the description text.
    
    let descriptionElements = elements.filter(element => element.y > descriptionTopElementY &&
        element.y < descriptionBottomLeftElement.y &&
        element.x > descriptionBottomLeftElement.x - 0.2 * descriptionBottomLeftElement.width);
    
    // Sort the description elements by Y co-ordinate and then by X co-ordinate (the Math.max
    // expressions exist to allow for the Y co-ordinates of elements to be not exactly aligned;
    // for example, hyphens in text such as "Retail Fitout - Shop 7").
    
    let elementComparer = (a, b) => (a.y > b.y + (Math.max(a.height, b.height) * 2) / 3) ? 1 : ((a.y < b.y - (Math.max(a.height, b.height) * 2) / 3) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    descriptionElements.sort(elementComparer);

    // Construct the description from the description elements.

    return descriptionElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ").replace(/ﬁ/g, "fi").replace(/ﬂ/g, "fl");
}

// Formats (and corrects) an address.

function formatAddress(address: string) {
    address = address.trim();
    if (address === "")
        return { text: "", hasSuburb: false, hasStreet: false };

    let tokens = address.split(" ");

    // It is common for an invalid postcode of "0" to appear at the end of an address.  Remove
    // this if it is present.  For example, "Bremer Range RD CALLINGTON 0".  The post code can
    // safely be remove because it will be derived later based on the suburb name.

    let postCode = tokens[tokens.length - 1];
    if (/^[0-9]{4}$/.test(postCode) || postCode === "O" || postCode === "0" || postCode === "D" || postCode === "[]" || postCode === "[J")
        tokens.pop();

    // Remove the state abbreviation (this will be determined from the suburb; it is always "SA").

    let state = tokens[tokens.length - 1];
    if (didyoumean(state, [ "SA" ], { caseSensitive: true, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 1, trimSpace: true }) !== null)
        tokens.pop();
    
    // Pop tokens from the end of the array until a valid suburb name is encountered (allowing
    // for a few spelling errors).

    let suburbName = null;
    for (let index = 1; index <= 4; index++) {
        let suburbNameMatch = didyoumean(tokens.slice(-index).join(" "), Object.keys(SuburbNames), { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true });
        if (suburbNameMatch !== null) {
            suburbName = SuburbNames[suburbNameMatch];
            tokens.splice(-index, index);  // remove elements from the end of the array           
            break;
        }
    }

    if (suburbName === null)  // suburb name not found (or not recognised)
        return { text: address, hasSuburb: false, hasStreet: false };

    // Expand an abbreviated street suffix.  For example, expand "RD" to "Road".

    let streetSuffixAbbreviation = tokens.pop() || "";
    let streetSuffix = StreetSuffixes[streetSuffixAbbreviation.toLowerCase()] || streetSuffixAbbreviation;

    // Allow minor spelling corrections in the remaining tokens to construct a street name.

    let streetName = (tokens.join(" ") + " " + streetSuffix).trim();
    let streetNameMatch = didyoumean(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true });
    if (streetNameMatch !== null)
        streetName = streetNameMatch;

    return { text: (streetName + ((streetName === "") ? "" : ", ") + suburbName).trim(), hasSuburb: true, hasStreet: (streetName.length > 0) };
}

// Gets and formats the address.

function getAddress(elements: Element[], assessmentNumberElement: Element, middleElement: Element) {
    let addressElements = getAboveElements(elements, assessmentNumberElement, assessmentNumberElement, middleElement);
    if (addressElements.length === 0)
        return undefined;
    
    // Construct the address from the discovered address elements (and attempt to correct some
    // spelling errors).

    let address = addressElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ").replace(/ﬁ/g, "fi").replace(/ﬂ/g, "fl").replace(/\\\//g, "V").replace(/‘/g, "").replace(/’/g, "").replace(/“/g, "").replace(/”/g, "").replace(/—/g, "").replace(/_/g, "").replace(/\./g, "").replace(/\-/g, "").replace(/\//g, "").replace(/!/g, "");
    if (address.startsWith("Dev Cost") || address.startsWith("LOT:") || address.startsWith("LOT ") || address.startsWith("HD:") || address.startsWith("HD "))  // finding this text instead of an address indicates that there is no address present
        return undefined;

    // If the address starts with a suburb then there may be a street name on the line above.

    let formattedAddress = formatAddress(address);

    if (!formattedAddress.hasStreet) {
        let streetElements = getAboveElements(elements, assessmentNumberElement, addressElements[0], middleElement);
        if (streetElements.length > 0) {
            let street = streetElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ").replace(/ﬁ/g, "fi").replace(/ﬂ/g, "fl").replace(/\\\//g, "V").replace(/‘/g, "").replace(/’/g, "").replace(/“/g, "").replace(/”/g, "").replace(/—/g, "").replace(/_/g, "").replace(/\./g, "").replace(/\-/g, "").replace(/\//g, "").replace(/!/g, "");
            if (!street.startsWith("Dev Cost") && !street.startsWith("LOT:") && !street.startsWith("LOT ") && !street.startsWith("HD:") && !street.startsWith("HD "))  // finding this text instead of an address indicates that there is no address present
                formattedAddress = formatAddress(street + " " + formattedAddress.text);
        }
    }

    if (formattedAddress.text === "" || formattedAddress.text.startsWith("Dev Cost") || formattedAddress.text.startsWith("Total Area"))
        return undefined;

    return formattedAddress.text;
}

// Parses the details from the elements associated with a single development application.

function parseApplicationElements(elements: Element[], startElement: Element, informationUrl: string) {
    // Find the "Assessment Number" or "Asses Num" text.

    let assessmentNumberElement = getAssessmentNumberElement(elements, startElement);
    if (assessmentNumberElement === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the \"Assessment Number\" or \"Asses Num\" text on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }

    // Find the "Applicant" text (a useful reference point).

    let applicantElement = elements.find(element =>
        element.y > startElement.y &&
        didyoumean(element.text, [ "Applicant" ], { caseSensitive: true, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 3, trimSpace: true }) !== null);

    // Find the "Builder" text (a useful reference point).

    let builderElement = elements.find(element =>
        element.y > startElement.y &&
        didyoumean(element.text, [ "Builder" ], { caseSensitive: true, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 3, trimSpace: true }) !== null);

    // One of either the applicant or builder elements is required in order to determine where
    // the description text starts on the X axis (and where the development application number
    // and address end on the X axis).

    let middleElement = (applicantElement === undefined) ? builderElement : applicantElement;
    if (middleElement === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the \"Applicant\" or \"Builder\" text on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }

    // Get the application number (allowing for a lot of common parsing errors).

    let applicationNumber = getRightRowText(elements, startElement, middleElement).trim().replace(/\s/g, "");
    applicationNumber = applicationNumber.replace(/[IlL\[\]\|’,!\(\)\{\}]/g, "/").replace(/°/g, "0").replace(/'\//g, "1").replace(/\/\//g, "1/").replace(/201\?/g, "2017").replace(/‘/g, "").replace(/'/g, "");  // for example, converts "17I2017" to "17/2017"
    if (applicationNumber.length >= 6 && /120[0-9][0-9]$/.test(applicationNumber))
        applicationNumber = applicationNumber.substring(0, applicationNumber.length - 5) + "/" + applicationNumber.substring(applicationNumber.length - 4);  // for example, converts "35612015" to "356/2015"

    if (applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }

    console.log(`    Found \"${applicationNumber}\".`);

    // Get the received date.

    let receivedDate: moment.Moment = undefined;
    let receivedDateElement = getReceivedDateElement(elements, startElement, middleElement);
    if (receivedDateElement !== undefined)
        receivedDate = moment(receivedDateElement.text.trim(), "D/MM/YYYY", true);

    // Get the description.

    let description = getDescription(elements, startElement, middleElement, receivedDateElement);

    // Get the address.

    let address = getAddress(elements, assessmentNumberElement, middleElement);
    if (address === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because an address was not found or parsed (searching upwards from the "Assessment Number" or "Asses Num" text).  Elements: ${elementSummary}`);
        return undefined;
    }

    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description === "") ? "No description provided" : description),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : ""
    };
}

// Finds the start element of each development application on the current PDF page (there are
// typically three development applications on a single page and each development application
// typically begins with the text "Dev App No.").

function findStartElements(elements: Element[]) {
    // Examine all the elements on the page that being with "D" or "d".
    
    let startElements: Element[] = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith("d"))) {
        // Extract up to 10 elements to the right of the element that has text starting with the
        // letter "d" (and so may be the start of the "Dev App No" or "Dev App No." text).  Join
        // together the elements to the right in an attempt to find the best match to the text
        // "Dev App No" or "Dev App No.".

        let rightElement = element;
        let rightElements: Element[] = [];
        let matches = [];

        do {
            rightElements.push(rightElement);
        
            // Allow for common misspellings of the "no." text.

            let text = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").replace(/n0/g, "no").replace(/n°/g, "no").replace(/"o/g, "no").replace(/"0/g, "no").replace(/"°/g, "no").replace(/“°/g, "no").toLowerCase();
            if (text.length >= 11)  // stop once the text is too long
                break;
            if (text.length >= 7) {  // ignore until the text is close to long enough
                if (text === "devappno" || text === "devappno.")
                    matches.push({ element: rightElement, threshold: 0 });
                else if (didyoumean(text, [ "DevAppNo", "DevAppNo." ], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 1, trimSpace: true }) !== null)
                    matches.push({ element: rightElement, threshold: 1 });
                else if (didyoumean(text, [ "DevAppNo", "DevAppNo." ], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true }) !== null)
                    matches.push({ element: rightElement, threshold: 2 });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 10);

        // Chose the best match (if any matches were found).

        if (matches.length > 0) {
            let bestMatch = matches.reduce((previous, current) =>
                (previous === undefined ||
                previous.threshold < current.threshold ||
                (previous.threshold === current.threshold && Math.abs(previous.text.length - "DevAppNo.".length) <= Math.abs(current.text.length - "DevAppNo.".length)) ? current : previous), undefined);
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
        let viewport = await page.getViewport(1.0);
        let operators = await page.getOperatorList();

        // Find and parse any images in the current PDF page.

        let elements: Element[] = [];

        for (let index = 0; index < operators.fnArray.length; index++) {
            if (operators.fnArray[index] !== pdfjs.OPS.paintImageXObject && operators.fnArray[index] !== pdfjs.OPS.paintImageMaskXObject)
                continue;

            // The operator either contains the name of an image or an actual image.

            let image = operators.argsArray[index][0];
            if (typeof image === "string")
                image = page.objs.get(image);  // get the actual image using its name
            else
                operators.argsArray[index][0] = undefined;  // attempt to release memory used by the image

            // Obtain the transform that applies to the image.  Note that the first image in the
            // PDF typically has a pdfjs.OPS.dependency element in the fnArray between it and its
            // transform (pdfjs.OPS.transform).

            let transform = undefined;
            if (index - 1 >= 0 && operators.fnArray[index - 1] === pdfjs.OPS.transform)
                transform = operators.argsArray[index - 1];
            else if (index - 2 >= 0 && operators.fnArray[index - 1] === pdfjs.OPS.dependency && operators.fnArray[index - 2] === pdfjs.OPS.transform)
                transform = operators.argsArray[index - 2];
            else
                continue;

            // Use the transform to translate the X and Y co-ordinates, but assume that the width
            // and height are consistent between all images and do not need to be scaled.  This is
            // almost always the case; only the first image is sometimes an exception (with a
            // scale factor of 2.083333 instead of 4.166666).

            let bounds: Rectangle = {
                x: (transform[4] * image.height) / transform[3],
                y: ((viewport.height - transform[5] - transform[3]) * image.height) / transform[3],
                width: image.width,
                height: image.height
            };
        }

        // Ignore extremely low height elements (because these can be parsed as text but are
        // very unlikely to actually be text; for example see the October 2016 PDF on page 19).
        // In some rare cases they may be valid (such as a full stop far from other text).

        elements = elements.filter(element => element.height > 2);

        // Sort the elements by Y co-ordinate and then by X co-ordinate.

        let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
        elements.sort(elementComparer);

        // Group the elements into sections based on where the "Dev App No." text starts (and
        // any other element the "Dev App No." elements line up with horizontally with a margin
        // of error equal to about the height of the "Dev App No." text; this is done in order
        // to capture the lodged date, which may be higher up than the "Dev App No." text).

        let applicationElementGroups = [];
        let startElements = findStartElements(elements);
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).  Allow some leeway vertically (add some extra height) because
            // in some cases the lodged date is a fair bit higher up than the "Dev App No." text
            // (see the similar leeway used in getReceivedDate).
            
            let startElement = startElements[index];
            let raisedStartElement: Element = {
                text: startElement.text,
                confidence: startElement.confidence,
                x: startElement.x,
                y: startElement.y - 3 * startElement.height,  // leeway
                width: startElement.width,
                height: startElement.height };
            let rowTop = getRowTop(elements, raisedStartElement);
            let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;

            // Extract all elements between the two rows.

            applicationElementGroups.push({ startElement: startElements[index], elements: elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop) });
        }

        // Parse the development application from each group of elements (ie. a section of the
        // current page of the PDF document).  If the same application number is encountered a
        // second time in the same document then this likely indicates the parsing of the images
        // has incorrectly recognised some of the digits in the application number.  In this case
        // add a suffix to the application number so it is unique (and so will be inserted into
        // the database later instead of being ignored).

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
