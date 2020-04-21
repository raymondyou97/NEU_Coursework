use ap;

-- calculate aggregated functions on the complete table 
SELECT COUNT(*) AS number_of_invoices,
    SUM(invoice_total- payment_total- credit_total)
    AS total_due
FROM invoices
WHERE invoice_totaL - payment_total- credit_total > 0;

-- this should be illegal statement but in MySQL is not illegal
SELECT COUNT(*) , payment_total from invoices;

SELECT count(*) from invoices;
SELECT * from invoices;
-- sense of the values

SELECT payment_total from invoices; 

-- field_list needs to contain the group by field_list 
SELECT vendor_id, sum(payment_total) from invoices group by vendor_id;

-- count the number of distinct vendor ids appearing in table 
SELECT COUNT(DISTINCT vendor_id) as vendor_nums from invoices;

-- do not remove duplicates
SELECT COUNT(vendor_id) as vendor_instances from invoices;

SELECT DISTINCT terms_id from invoices;
-- determine the number of vendors for each terms_id 
SELECT terms_id, COUNT(DISTINCT vendor_id)
 as vendor_nums from invoices group by terms_id;

-- identify the invoices that are above the average payment total and return 
-- the amont they are above the average payment
USE ex;
SELECT invoice_id, invoice_date,

payment_total - (select avg(payment_total) from paid_invoices) aboveAvg
FROM paid_invoices
where payment_total > (SELECT AVG(payment_total) FROM paid_invoices); 

CREATE TABLE above_avg
SELECT invoice_id, invoice_date, 
        payment_total
FROM paid_invoices
where payment_total > (SELECT AVG(payment_total) FROM paid_invoices); 

-- HAVING clause allows you to create a filter for the aggregated data
use ap; 
SELECT vendor_id, sum(payment_total) from invoices group by vendor_id
        having sum(payment_total) > 150;
