/* ALL CONDITION MUST BE TRUE FOR ALL THE VALUES RETURNED BY THE SUBQUERY 
example x > ALL (1,2) same as x > 2
        x < ALL (1, 2) same as x < 1
        x = ALL (1,2) same as x = 1 and x =2 only makes sense if returns 1 value or the same value
        x <> ALL (1,2) same as x NOT IN (1,2) 
*/

SELECT vendor_name, invoice_number, invoice_total
FROM invoices i JOIN vendors v ON i.vendor_id = v.vendor_id
WHERE invoice_total > ALL
    (SELECT invoice_total
     FROM invoices
     WHERE vendor_id = 34)
ORDER BY vendor_name;