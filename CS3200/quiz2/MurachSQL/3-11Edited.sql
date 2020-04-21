-- Examples of AND and OR
-- Orde of precedence NOT, AND, IR
-- 
SELECT invoice_number, invoice_date, invoice_total, 
(invoice_total - payment_total - credit_total) AS balance_due
FROM invoices
WHERE invoice_date > '2014-07-03' OR invoice_total > 500
  AND invoice_total - payment_total - credit_total > 0;  
  
 -- Equivalent to the query above
 -- Parentheses inserted to exlicitly show precedence
SELECT invoice_number, invoice_date, invoice_total, 
(invoice_total - payment_total - credit_total) AS balance_due
FROM invoices
WHERE (invoice_date > '2014-07-03' OR invoice_total > 500)
  AND invoice_total - payment_total - credit_total > 0;