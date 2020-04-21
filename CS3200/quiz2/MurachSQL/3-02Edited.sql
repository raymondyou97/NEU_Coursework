use ap;

-- SELECT all fields from a table 
SELECT * from invoices;
--  SELECT fields from a total order the output by invoice_total
-- in descending order


SELECT invoice_number, invoice_date, invoice_total
FROM invoices
ORDER BY invoice_total DESC;

-- Create a calculated field named total_credits 
-- Specify a where criterion 
SELECT invoice_id, invoice_total,
       credit_total + payment_total AS total_credits
FROM invoices
WHERE invoice_id = 17;
 
 -- BETWEEN used with a date variable 
SELECT invoice_number, invoice_date, invoice_total
FROM invoices
WHERE invoice_date BETWEEN '2014-06-01' AND '2014-06-30'
ORDER BY invoice_date;
 
 -- another filter using the WHERE clause 
SELECT invoice_number, invoice_date, invoice_total
FROM invoices
WHERE invoice_total > 50000;