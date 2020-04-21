/* IN can provide a canned list or a subquery */
USE ap;

/* IN example with a subquery */

SELECT vendor_id, vendor_name, vendor_state
FROM vendors
WHERE vendor_id  IN
    (SELECT DISTINCT vendor_id
     FROM invoices)
ORDER BY vendor_id;

/* IN example with a subquery */

SELECT vendor_id, vendor_name, vendor_state
FROM vendors
WHERE vendor_id  IN
    (34, 37, 48)
ORDER BY vendor_id;