USE ap;
/* TEST WHETHER A COMPARISON IS TRUE FOR ANY OF THE RECORDS RETURNED BY A SUBQUERY 
   x > any(1,2) x > 1
   x < any(1, 2) x < 2
   x = ANY(1,2) x in (1,2)
   x <> ANY(1,2) (x <> 1) OR (x <> 2) 
   SOME is a synonym for ANY - so it translate the same 
*/
SELECT vendor_name, invoice_number, invoice_total
FROM vendors JOIN invoices ON vendors.vendor_id = invoices.invoice_id
WHERE invoice_total < ANY
    (SELECT invoice_total
     FROM invoices
     WHERE vendor_id = 115);