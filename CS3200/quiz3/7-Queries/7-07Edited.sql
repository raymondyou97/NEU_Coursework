-- Example: nested query
USE ap;

-- find invoices that are above the average invoice price 
SELECT vendor_id, invoice_number, invoice_total
FROM invoices i
WHERE invoice_total >
    (SELECT AVG(invoice_total)
     FROM invoices
     )  
ORDER BY vendor_id, invoice_total;

-- correlated query use a value from the outer query to limit values for the inner query
-- find invoices that are above the average invoice for the specific vendor 
-- need an average per vendor 
-- like a JOIN between the INNER and OUTER query 
SELECT vendor_id, invoice_number, invoice_total
FROM invoices i
WHERE invoice_total >
    (SELECT AVG(invoice_total)
     FROM invoices j
     WHERE j.vendor_id = i.vendor_id)  
ORDER BY vendor_id, invoice_total;


