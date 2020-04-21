USE ex;

SELECT department_name, d.department_number, last_name
FROM departments d 
	JOIN employees e
    ON d.department_number = e.department_number
ORDER BY department_name;


-- More OUTER JOIN examples
-- find employees and their assigned departments
-- also return departments without any assigned employees
SELECT department_name, d.department_number, last_name
FROM departments d 
    LEFT JOIN employees e
    ON d.department_number = e.department_number
ORDER BY department_name;

-- return employees and their assigned departments 
-- also return employees that have not been assigned to a department
SELECT department_name, d.department_number , e.department_number, last_name
FROM departments d 
    RIGHT JOIN employees e
    ON d.department_number = e.department_number
ORDER BY department_name;

-- return a row for each department/employee combination
-- First LEFT JOIN ensure all departments show in result 
-- Second LEFT JOIN ensure we do not lose the departments from the first JOIN
-- also include the projects employees are assigned to 
SELECT department_name, last_name, project_number
FROM departments d
    LEFT JOIN employees e
        ON d.department_number = e.department_number
    LEFT JOIN projects p
        ON e.employee_id = p.employee_id
ORDER BY department_name, last_name;

-- you can mix both INNER and OUTER JOINsprojects
-- compare to an inner join on both department/ employees
-- we only have records for employees assigned to a department 
SELECT department_name, last_name, project_number
FROM departments d
    JOIN employees e
        ON d.department_number = e.department_number
    LEFT JOIN projects p
        ON e.employee_id = p.employee_id
ORDER BY department_name, last_name;

SELECT department_name, last_name, project_number
FROM departments d
    JOIN employees e
        ON d.department_number = e.department_number
	JOIN projects p
        ON e.employee_id = p.employee_id
ORDER BY department_name, last_name;