USE ap;

select vendor_id, invoice_id from invoices;

SELECT vendor_id, count(*) AS num_invoices FROM invoices
GROUP by vendor_id;

SELECT vendor_id, ROUND(AVG(invoice_total), 2) AS average_invoice_amount
FROM invoices
GROUP BY vendor_id
ORDER BY average_invoice_amount DESC;

SELECT vendor_id, ROUND(AVG(invoice_total), 2) AS average_invoice_amount
FROM invoices
GROUP BY vendor_id
HAVING AVG(invoice_total) > 2000
ORDER BY average_invoice_amount DESC;