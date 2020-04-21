-- Example of an INNER JOIN
-- where  we are aliasing the table names
-- the WHERE clause can be used to further restrict the records in the result set

USE ap;

SELECT invoice_number, vendor_name, invoice_due_date,
    invoice_total - payment_total - credit_total AS balance_due
FROM vendors v JOIN invoices i
    ON v.vendor_id = i.vendor_id
WHERE invoice_total - payment_total - credit_total > 0
ORDER BY invoice_due_date DESC;

-- another example of a JOIN across a foreign key
SELECT invoice_number, line_item_amount, line_item_description
FROM invoices JOIN invoice_line_items line_items
    ON invoices.invoice_id = line_items.invoice_id
WHERE account_number = 540
ORDER BY invoice_date;