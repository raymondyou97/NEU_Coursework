-- example of an equi-join: using the same named field from both tables
-- simplify the code with the USING clause
-- tables must be joined by a column that has the same name in both tables
-- equality is the operator for the USING clause

SELECT invoice_number, vendor_name
FROM vendors 
    JOIN invoices USING (vendor_id)
ORDER BY invoice_number;

-- INNER JOIN of employees assigned to departments
-- find the projects for the employees assigned to departments
-- multiple fields for the join? USING  (field1, field2)
SELECT department_name, last_name, project_number
FROM departments
    JOIN employees USING (department_number)
    LEFT JOIN projects USING (employee_id)
ORDER BY department_name;