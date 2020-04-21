-- Examples of limit
-- print 5 tuples from the result set 
SELECT vendor_id, invoice_total
FROM invoices
ORDER BY invoice_total DESC
LIMIT 5;
-- skip the first two rows in the result set
-- limit the output to three rows
SELECT invoice_id, vendor_id, invoice_total
FROM invoices
ORDER BY invoice_id
LIMIT 2, 3;

-- skip the first 100 rows in the result set 
-- limit the output to 1000 rows 
SELECT invoice_id, vendor_id, invoice_total
FROM invoices
ORDER BY invoice_id
LIMIT 100, 1000;