-- prepared statements use dynamic SQL to
-- build a string that contains the SQL statement
-- then use PREPARE, EXECUTE, and DEALLOCATE statements
-- to execute, the SQL statement contained in the string
-- can change the name of the fields and the tables in the query
-- With prepared statements, the query plan is saved so you can re-execute 
-- the same plan with different data over and over 



-- prepared statement example 
use scratch;
SET @a := "a";
SELECT * FROM INFORMATION_SCHEMA.TABLES;
select @g := column_name FROM INFORMATION_SCHEMA.COLUMNS 
    WHERE TABLE_SCHEMA = 'scratch' and table_name = 'country';
    
use scratch;
SET @a := "code";    
SET @b := "country";
SET @s := CONCAT ("select ", @a, " FROM ", @b); -- example dynamic SQL
PREPARE stmt FROM @s;
EXECUTE stmt;

SET @s1 := CONCAT ("select ", @g, " FROM ", @b);
PREPARE stmt FROM @s1;
select @g;

EXECUTE stmt;
DEALLOCATE PREPARE stmt;

-- prepared statement example 
use starwarsfinal;
-- can concatentate table names and fields together into a statement 
SET @a := "character_name";
SET @b := "characters";
SET @c := "'Darth Vader'";
SET @s := CONCAT ("select ", @a, " FROM ", @b, " where ", @a, " = " , @c);
PREPARE stmt FROM @s;
SELECT @s;

EXECUTE stmt;
DEALLOCATE PREPARE stmt;

-- cannot change table names and field names in a prepare statement 
use starwarsfinal;

SET @c2 := "Darth Vader";
PREPARE stmt5 FROM "select * FROM characters where character_name = ?";
EXECUTE stmt5 USING @c2;
SET @c2 := "C-3 PO";
EXECUTE stmt5 USING @c2;
DEALLOCATE PREPARE stmt5;

-- prepared statements protect you from malicious users trying to get access
-- to data they should not have access to 

--  a good user's name
use world;
set @name = "'algeria'"; 
set @query = concat('SELECT * FROM country WHERE name =', @name, ';');
select  @query;
PREPARE stmt6 FROM @query;
EXECUTE stmt6;

-- protection against SQL injection binding variables 
-- user input that uses SQL Injection
use world;
SELECT * FROM country WHERE name = 'algeria' or 1;

set @name_bad = "'algeria' or 1"; 
set @query = 'SELECT * FROM country WHERE name = ?'; -- sets parameter for name value to match

set @badquery = concat("SELECT * FROM country WHERE name =", @name_bad, ";");
-- treats code as TEXT string no arguments passed 

select  @query;
select  @badquery;
-- cannot prepare the statement since prepare expects field names 
PREPARE stmt11 FROM @query;
EXECUTE stmt11 using @name_bad; -- returns nothing from the table 

PREPARE stmt10 FROM @badquery;
EXECUTE stmt10; -- returns the whole table SQL injection example 
