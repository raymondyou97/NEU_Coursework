use ap;

-- More system defined function examples 
-- LEFT(string,numCharactersToExtract)
SELECT vendor_contact_first_name, vendor_contact_last_name,
       CONCAT(LEFT(vendor_contact_first_name, 1), 
              LEFT(vendor_contact_last_name, 1)) AS initials
FROM vendors;

-- CAN change the format of a date with DATE_FORMAT function
SELECT invoice_date,
       DATE_FORMAT(invoice_date, '%m/%d/%y') AS 'MM/DD/YY',
       DATE_FORMAT(invoice_date, '%e-%b-%Y') AS 'DD-Mon-YYYY'
FROM invoices;

-- ROUND function, 
-- first argument value to round
-- second argument number of digits after the decimal
SELECT invoice_date, invoice_total,
       ROUND(invoice_total) AS nearest_dollar,
       ROUND(invoice_total, 1) AS nearest_dime
FROM invoices;

