use world;


select @test := 2;
-- command to set the value of a variable
-- variables not initialized are assumed to be NULL and of date type text
set @test := 2;
select @test + 1; -- returns 3
-- can set a variable equal to the return of a query
select @numB := count(*) from country where name like 'B%';
select @numB;
select @numA := count(*) from country where name like 'A%';
select @numA, @numB;

-- You can store values from a query into a variable
-- with the set command can use the simpler = symbol 
-- can retrieve specific values from variables into variables 
SET @code = 0, @name = '';
-- assign values to code and name 
SELECT code, name INTO @code, @name FROM country order by code desc limit 1;
SELECT @code, @name;
select * from country where name = 'Zimbabwe';

SET @code = 0, @name = '';
-- will return a different code, and name since we are ordering the result set differently 
SELECT code, name INTO @code, @name FROM country order by code limit 1;
SELECT @code, @name;
-- variables do not need to declared so any typo is a variable 
SELECT @cod, @name;

-- creating a counter variable in the result set
select @counter := @counter + 1 as counter, country.* from 
 ( select @counter := 0  ) v cross join  country order by name;

 -- assign it before call the SQL statement 
 set @counter :=0;
 select @counter := @counter + 1 as counter, country.* from  country;
 
 -- we can do an aggregated total across groups using a user session variable
 select t.continent, t.name, t.c rowcount, @x:=@x+t.c cumulativecount
 FROM
 ( select @x := 0) a,
 ( SELECT name, continent, sum(population) as c
FROM
   country
 GROUP BY name, continent order by continent) t ; 


-- we can do cumulative totals per continent 
select t.continent, t.name, t.c rowcount , 
       @x:=if(@same_value=continent, @x+t.c, t.c) cumulativecount , 
       @same_value:=continent as holder
 FROM
 ( select @x := 0, @same_value:='') a cross join 
 ( SELECT name, continent, population as c
FROM
   country
  order by continent) t ; 
 
 
-- we can do cumulative totals per continent 
select t.continent, t.name, t.c rowcount , 
       @x:=if(@same_value=continent, @x+t.c, t.c) cumulativecount , 
       @same_value:=continent as holder
 FROM
 ( select @x := 0, @same_value:='') a cross join 
 ( SELECT name, continent, sum(population) as c
FROM
   country
 GROUP BY name, continent order by continent) t ; 
 
 -- DO I need the group by 
 -- we can do cumulative totals per continent 
select t.continent, t.name, t.c rowcount , 
       @x:=if(@same_value=continent, @x+t.c, t.c) cumulativecount , 
       @same_value:=continent as holder
 FROM
 ( select @x := 0, @same_value:='') a cross join 
 ( SELECT name, continent, population as c
FROM
   country
  continent order by continent) t ; 
 
 
--  SQL 
use scratch; 
drop table if exists test;
create table 
test (a INT primary key auto_increment, b int, rand_column float);
insert into test (b) VALUES  (1) ,(2), (3), (4), (5), (6);
set @added:=0;

select * from test;

update test set rand_column=@added:=@added+1 order by rand();

select * from test;

-- SQL control flow statements 
-- - IF ... ELSEIF .... ELSE....alter
-- -- CASE ....WHEN EXPRESSION THEN ... WHEN EXPRESSION2 THEN ... ELSE END 
-- - WHILE ...DO...LOOP
-- - REPEAT ... UNTIL ... END ... REPEAT
-- -- DECLARE CURSOR FOR
-- -- DECLARE ... HANDLER 
use scratch;
-- Example of a procedure using IF 
DROP PROCEDURE IF EXISTS IFCODE;
DELIMITER $$
CREATE PROCEDURE IFCODE(IN a INT, OUT mesg VARCHAR(30)) 
BEGIN 
IF a =10 THEN SET mesg = 'value 10';
   else set mesg = 'other value';
SELECT mesg;
end if;
END$$

SET @MESSAGE = '';
set @a = 10;

CALL IFCODE(@a, @MESSAGE);
SELECT @MESSAGE;

SET @MESSAGE = '';
-- CAN PASS A VALUE AS AN IN ARGUMENT 
CALL IFCODE(10, @MESSAGE);
SELECT @MESSAGE;



		