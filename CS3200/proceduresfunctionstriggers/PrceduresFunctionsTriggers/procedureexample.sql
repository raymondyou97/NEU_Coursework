-- Look at the support for procedures and functions
USE information_schema;
select * from ROUTINES;
USE sakila;
show create function sakila.get_customer_balance;

show create procedure sakila.film_in_stock;
-- show how to modify the code 
SET @RESULT = 0;
SET @IN1 = 1;
SET @IN2 = 1;
CALL film_in_stock(@IN1,@IN2, @RESULT);
SELECT @RESULT;


-- Simple example of a function that prints a message
-- USE Select to retrieve content 
 DROP PROCEDURE IF EXISTS test;
 DELIMITER $$
 
 CREATE PROCEDURE test()
 BEGIN 
 SELECT "This is a test" as msg; 
 END$$
 DELIMITER ;
  CALL test();

 

 DELIMITER $$
 
CREATE PROCEDURE counter() 
BEGIN 
DECLARE x INT; -- example of DECLARE
SET x = 1; -- EXAMPLE OF SET
WHILE x <= 5 DO -- WHILE LOOP 
    SET x = x + 1;
 END WHILE; -- CLOSE OF WHILE LOOP 
SELECT x; -- 6 -- THIS WILL PRINT THE VALUE OF THE VARIABLE 
END$$ 
DELIMITER ;

-- Example on how to call a function 
call counter();
--
-- To get back a value from a procedure using an OUT or INOUT parameter, 
-- pass the parameter by means of a user variable, 
-- and then check the value of the variable after the procedure returns.
set @fromprocedure := 0;

USE world;

DROP procedure if exists getcountrylifeexpectancy;
DELIMITER $$
CREATE PROCEDURE 
getcountrylifeexpectancy
(    IN rlifeexpectancy float(3,1), 
     OUT countries varchar(500)
) 
BEGIN 

DECLARE row_not_found TINYINT DEFAULT FALSE;
DECLARE lname char(52);
DECLARE lcontinent char(40);
DECLARE holder varchar(500);

DECLARE country_cursor CURSOR FOR 
	SELECT Name, Continent from country 
		WHERE lifeexpectancy = rlifeexpectancy order by name;
        
DECLARE CONTINUE HANDLER FOR NOT FOUND
  SET row_not_found = TRUE;
  
OPEN country_cursor;
WHILE row_not_found = FALSE DO
 FETCH country_cursor INTO lname, lcontinent;
  set countries:=concat( lname, ' ', lcontinent);
 
 END WHILE;
 CLOSE country_cursor;
SELECT countries;
 END$$
 
 -- SET THE DELIMITER BACK TO ITS DEFAULT 
 DELIMITER ;
 
set @countries = 'COUNTRIES:';
call getcountrylifeexpectancy(80.7,@countries);
SELECT @countries;


select * from country where lifeexpectancy = 80.7;
