-- Example of a INNER JOIN
-- INNER key word is optional as INNER JOIN is the default customers
USE  ap;

SELECT invoice_number, vendor_name
FROM vendors INNER JOIN invoices
    ON vendors.vendor_id = invoices.vendor_id
ORDER BY invoice_number;

select * from invoices;
select * from vendors;