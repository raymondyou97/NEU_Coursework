-- CROSS JOIN EXAMPLE
-- CROSS JOIN produces a result set that includes each row from the first 
-- table joined with each row from the second table
-- it is a cartesian product of the two tables
-- there is no qualifying clause for the result set
-- how many records in the result set?? number of tuples in table 1 * number of tuples in table 2
SELECT departments.department_number, department_name, employee_id, 
    last_name
FROM departments CROSS JOIN employees
ORDER BY departments.department_number;

-- Implicit representation for the CROSS JOIN
SELECT departments.department_number, department_name, employee_id, 
    last_name
FROM departments, employees
ORDER BY departments.department_number;