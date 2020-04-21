USE ap;
-- A correlated subquery, we use the values in the outer most query
-- within the inner most query 
-- example also uses the NOT EXISTS construct 
-- EXISTS tests to see if the subquery returns a result set 
-- not exists does not return a result set - it returns TRUE OR FALSE 

-- returns all the vendors in the vendors tables that do not have invoices 
SELECT vendor_id, vendor_name, vendor_state
FROM vendors
WHERE NOT EXISTS
    (SELECT * 
     FROM invoices
     WHERE invoices.vendor_id = vendors.vendor_id);
     
-- Other ways to write this query???








SELECT vendor_id, vendor_name, vendor_state
FROM vendors
WHERE vendor_id NOT IN
    (SELECT DISTINCT vendor_id
     FROM invoices)
ORDER BY vendor_id;

SELECT v.vendor_id, vendor_name, vendor_state
FROM vendors v LEFT JOIN invoices i
    ON v.vendor_id = i.vendor_id
WHERE i.vendor_id IS NULL
ORDER BY v.vendor_id;     