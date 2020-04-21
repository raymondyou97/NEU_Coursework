-- use ap;
-- Assigning a variable name 
SELECT invoice_total, payment_total, credit_total,
       invoice_total - payment_total - credit_total AS balance_due
FROM invoices;

-- figuring out arithmetic precedence
-- using paenthese to change the default order of operations
-- parentheses have highest precedence
-- followed by multiplication and division
-- followed by subtraction and division 
SELECT invoice_id, 
       invoice_id + 7 * 3 AS multiply_first, 
       (invoice_id + 7) * 3 AS add_first
FROM invoices;

-- Data type returned determned by the data type source
-- % modulo function
SELECT invoice_id, 
       invoice_id / 3 AS decimal_quotient,
       invoice_id DIV 3 AS integer_quotient,
       invoice_id % 3 AS remainder
FROM invoices;