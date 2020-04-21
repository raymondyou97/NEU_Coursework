-- Example of an LEFT OUTER JOIN
-- Outer Joins allow you to specify that all of the records from one of the tables
-- should be part of the result set
-- will also pull all records in the other table that satisfies the JOIN condition
-- NULL values are returned for the fields without a matching value
-- the OUTER keyword is optional 

-- this query returns at least one  record for each vendor
-- and appends the invoice fields to the corresponding vendor record
-- useful for tracking vendors without activiy

SELECT vendor_name, invoice_number, invoice_total
FROM vendors LEFT JOIN invoices
    ON vendors.vendor_id = invoices.vendor_id
ORDER BY vendor_name;

SELECT vendor_name, invoice_number, invoice_total
FROM vendors  JOIN invoices
    ON vendors.vendor_id = invoices.vendor_id
ORDER BY vendor_name;