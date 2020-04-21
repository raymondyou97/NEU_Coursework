use ap;
-- large library of system defined functions
-- CONCAT needs some formatting of strings 
SELECT vendor_city, vendor_state, CONCAT(vendor_city, vendor_state)
FROM vendors;

-- CONCAT needs some formatting of strings 
SELECT vendor_name,
       CONCAT(vendor_city, ', ', vendor_state, ' ', vendor_zip_code) 
           AS address
FROM vendors;

-- Even more formatting of strings 
-- CONCAT(string1,string2, ...)
-- format string value using literal values 
-- need additional  2 '' to include an ' in a string
-- quoting the quote to not be interpreted 
SELECT CONCAT(vendor_name, '''s Address: ') AS Vendor,
       CONCAT(vendor_city, ', ', vendor_state, ' ', vendor_zip_code) 
           AS Address
FROM vendors;

