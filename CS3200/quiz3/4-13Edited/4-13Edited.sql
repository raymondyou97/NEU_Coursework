-- Same definition as SET UNION
-- create a result set that contains elements from both sets
-- remove duplicates acress the sets

-- in order for the sets to be UNION compatible 
-- 1) the number of columns need to be the same in both sets
-- 2) and the corresponding data types must be  compatible
--  if there are differences in the colun names the first table
-- determines the field names in the result set 
SELECT 'Active' AS source, invoice_number, invoice_date, invoice_total
    FROM active_invoices
    WHERE invoice_date >= '2014-06-01'
UNION
    SELECT 'Paid' AS source, invoice_number, invoice_date, invoice_total
    FROM paid_invoices
    WHERE invoice_date >= '2014-06-01'
ORDER BY invoice_total DESC;

-- UNION  ALL does not remove duplicates from the result set 
SELECT 'Active' AS source, invoice_number, invoice_date, invoice_total
    FROM active_invoices
    WHERE invoice_date >= '2014-06-01'
UNION ALL 
    SELECT 'Paid' AS source, invoice_number, invoice_date, invoice_total
    FROM paid_invoices
    WHERE invoice_date >= '2014-06-01'
ORDER BY invoice_total DESC;

use ex; 
-- will remove duplicate customer who is an employee 
SELECT first_name, last_name from employees 
UNION
SELECT customer_first_name as first_name, customer_last_name from customers ORDER by last_name;

-- will remove duplicate customer who is an employee 
SELECT first_name, last_name from employees 
UNION ALL 
SELECT customer_first_name as first_name, customer_last_name from customers ORDER by last_name;
