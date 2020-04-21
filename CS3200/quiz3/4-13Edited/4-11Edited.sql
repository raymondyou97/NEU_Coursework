USE ap;

-- Example of a NATURAL JOIN
-- JOIN is done across all fields that are common across the two tables
-- Natural JOIN  is not the safest method for writing a JOIN 
SELECT invoice_number, vendor_name
FROM vendors 
    NATURAL JOIN invoices
ORDER BY invoice_number;
 
USE ex;
-- JOIN across the departments and employees
-- what are the common fields ?
SELECT department_name AS dept_name, last_name, project_number
FROM departments
    NATURAL JOIN employees -- what fields compose the JOIN condition??
    LEFT JOIN projects USING (employee_id)
ORDER BY department_name;