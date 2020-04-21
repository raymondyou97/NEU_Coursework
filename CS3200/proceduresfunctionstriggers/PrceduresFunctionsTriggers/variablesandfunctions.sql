-- DATE OPERATIONS
--
--
--
-- returns the current date and time 
select now(); 
select current_timestamp();
-- returns the current date 
select curdate();
select current_date();
-- returns the current time
select curtime();
select current_time();

-- Returns the numeric representation of the part of the provided date 
-- day of month date for  October 1  or '2015-10-01' returns 1
-- can pass datetime or a date variable 
select dayofmonth(curdate());
select dayofmonth(now());
-- here's the format of a date value
select dayofmonth('2015-12-25');

-- returns the numeric count since the first of the year so limited 1 to 366
select dayofyear(now());
select dayofyear('2015-11-11');

-- returns 1 through 7 , Sunday = 1, Saturday = 7 
select dayofweek(now());


-- returns Sunday - Saturday 
select dayname(now());
select dayname('2015-12-25');
select dayname('2015-12-25 12:12:12');


-- date arithmetic DATEDIFF, DATEADD SQL Standard 
-- hoe many days transpired from date1 to date 2
SELECT DATEDIFF('2015-10-30 23:59:59','2014-10-30');
-- will get a negative number of days frim datediff if 2nd date is a later date 
SELECT DATEDIFF('2015-9-9 23:59:59','2015-12-11');
-- common query to measure how many days have transpired since an event
SELECT DATEDIFF( NOW(), '2015-9-9 23:59:59' );

-- Can specify an interval to be added or substracted from a date 
--  adddate(date, INTERVAL nn measure) 
SELECT ADDDATE('2015-10-30 23:59:59',INTERVAL 21 DAY);
-- can use negative numbers
SELECT ADDDATE('2015-10-30 23:59:59',INTERVAL -41 DAY);
-- there are other interval types 
SELECT SUBDATE('2015-10-30 23:59:59',INTERVAL 24 MONTH);

SELECT SUBDATE('2015-10-30 23:59:59',INTERVAL 24 YEAR);

-- can retrieve portions of a date 
-- remember now() returns the current date 
SELECT EXTRACT(YEAR FROM NOW() );
SELECT EXTRACT(MONTH FROM NOW() );
SELECT EXTRACT(DAY FROM NOW() );
SELECT EXTRACT(QUARTER FROM NOW() );

-- can make a date from a day number 
-- My SQL uses the gregorian calendar 
-- so number of days 730669  where day 1 = jan 1 , in year 0000 
-- has issues with dates before 1582 due to the cross over from julian calendar to gregorian calendar 
select from_days(1);
-- get us close to our timeframe 
select from_days(730669);
select from_days(736249);

-- Can also piece a date together given a year 
-- and the number of days since the beginning of that year 
select makedate(2000, 15);

-- do not forget about leap years that have 366 days 
select makedate(2000, 366);

-- can increase the year you are interested in 
select makedate(2000, 380);

-- return the date of the last day in the month specified in the passed date 
-- convenient for creating calendar layouts 
select last_day(now());


-- NULL comparisons / functions
--
-- MySQL specific comparison operator 
-- will match the UNDEFINED VALUE
SELECT NULL <=> NULL ;
-- returns the first argument that is not null 
SELECT coalesce(NULL, '', "5", 5) ;
-- one interesting thing is that coalesce accepts multiple data types as arguments

-- table example
use scratch;
-- create a table for the exercise
drop table if exists showcoalesce;
create table  showcoalesce(a int, b int, c varchar(30));
insert into showcoalesce (b,c) VALUES (1, 'HELLO');
insert into showcoalesce (b) VALUES (2);
insert into showcoalesce(a,c) VALUES (3, 'END'); 
insert into showcoalesce(b,c) VALUES (3, 'END'); 
insert into showcoalesce(c) VALUES ( 'last'); 
insert into showcoalesce(a,b) VALUES ( 4,4); 
insert into showcoalesce(a,b) VALUES ( 5,2); 
-- look at the table 
-- review the values 
select * from showcoalesce;

-- will return first non NULL value
SELECT coalesce(a,b,c) from showcoalesce;
-- what if they are all NULL - what does it return
SELECT coalesce(a,b) from showcoalesce;

--  how can we have different types in the return set ???
-- let's create a table and see the type associated with this coalesced field
drop table if exists what;
CREATE TABLE WHAT SELECT coalesce(a,b,c) from showcoalesce;
DESCRIBE WHAT;
drop table if exists what2;
CREATE TABLE WHAT2 SELECT coalesce(a,b) from showcoalesce;
DESCRIBE WHAT2;

-- Many of the functions need to compare the data types of the passed arguments to determine
-- what data type should be used in the result set and what comparison operator is appropriate 
-- function will compare using the larger extended data type so promote ints to reals
-- use binary character strings when comparing text to numbers etc. 

-- return 2nd argument if 1st argument is NULL 
SELECT a,b,c, ifnull(a,b)  FROM showcoalesce;



-- Check to see if arguments are equal
-- If equal then return NULL 
-- if not equal return argument 1
SELECT nullif(2,1);
-- pass equal values 
SELECT nullif(2,2);
-- does data type matter
SELECT nullif(2,'2');

select nullif(1,NULL);

-- return NULL if arguments are equal 
SELECT a,b, nullif(a,b) from showcoalesce;
-- Excercise 
-- state the origin of each nullif(a,b) result 
--  from Column a or the result of the failed equality 
-- what does this return???
SELECT NULL = NULL;


-- String functions 
use world;
-- concatentate strings together 
select concat(name, ', ' , continent) from country;
-- side tangent on aliases 
-- can I immediately use my aliases in the field list ??
select concat(name, ', ' , continent) as cc, char_length(cc) from country;

-- where can I use my aliases in my other clauses 
select concat(name, ', ' , continent) as cc,
   char_length(concat(name, ', ' , continent)) from country
  where cc like 'A%';
  
  -- cc variable not currently defined in this level of the sql statement
  -- here is what you would do to match the value
  select concat(name, ', ' , continent) as cc,
   char_length(concat(name, ', ' , continent)) from country
  where concat(name, ', ' , continent)  like 'A%';
  

-- locate locates the starting character position of the first occurring substring in a string
-- returns 0 if the substring is not located in the string
select continent, locate('A', continent) apos from country;
-- can group by the function return value 
select continent, locate('A', continent) apos from country group by continent, apos;
-- can use the location to determine how much you copy

-- describe the set without the conditional phrase
-- can nest the functions 
-- rtrim - remove trailing white space , ltrim remove leading white space 
select 
   rtrim(ltrim(left(continent, length(continent) - locate('america',continent)))) , 
   continent from country
 where continent like '%america';
 
 -- sometimes easier to trim off leading and trailing white space as oppose to try
 -- and define a rule for 
 -- calculating begin point  and endpoint of a substring 
 select  left(continent, length(continent) - locate('america',continent)) , 
		length(left(continent, length(continent) - locate('america',continent))) notrim,
        length(ltrim(rtrim(left(continent, length(continent) - locate('america',continent))))) trimmed, continent from country
 where continent like '%america';
 
 -- trim looks for both trailing and leading white space 
 select  left(continent, length(continent) - locate('america',continent)) , 
		length(left(continent, length(continent) - locate('america',continent))) notrim,
        length(trim(left(continent, length(continent) - locate('america',continent)))) trimmed, 
        continent from country
 where continent like '%america';
 
 -- can replace a string in another string
 -- can  insert a substring in a string 
 
 use scratch;
 -- replace a capital A with aa
 select 'ABCDEFG', replace('ABCDEFG', 'A', 'aa');
 -- is replace case sensitive ??
 select 'ABCDEFG', replace('ABCDEFG', 'a', 'aa');
 -- will return the original string if nothing is replaced
 -- this is typically the functionality you want
 select 'ABCDEFG', replace('ABCDEFG', 'A', 'aa');
 
 
 -- INSERT(str,position,length,substring);
 -- insert substring at position position removing length characters
 -- Returns the original string if position is not within the length of the string. 
 -- Replaces the rest of the string from position position 
 -- if length is not within the length of the rest of the string.
 
 SELECT 'ABCDEFG', LENGTH('ABCDEFG'), INSERT('ABCDEFG',2,1,'BOY');
 
 -- send the length of the string will addd the substring as a suffix 
 SELECT 'ABCDEFG', LENGTH('ABCDEFG'), INSERT('ABCDEFG',2,LENGTH('abcdefg'),'BOY');
 
 -- replace the entire string
 SELECT 'ABCDEFG', LENGTH('ABCDEFG'), INSERT('ABCDEFG',1,LENGTH('abcdefg'),'BOY');
 
 -- does not change the string if starting position beyond the length of the string
 -- why the +2 as oppose to +1
 SELECT 'ABCDEFG', LENGTH('ABCDEFG'), INSERT('ABCDEFG',length('ABCDEFG') +2,1,'BOY');
 
 -- does this generate the same results as the above line?
 SELECT 'ABCDEFG', LENGTH('ABCDEFG'), INSERT('ABCDEFG',length('ABCDEFG') +1,1,'BOY');
 
 -- end of string is a null values character, so can still insert at length + 1
 -- this is the way to add a suffix 
 SELECT 'ABCDEFG', LENGTH('ABCDEFG'), INSERT('ABCDEFG',length('ABCDEFG') + 1,1,'BOY');
 
 
 -- Regular expressions
 -- Function found in many programming languages, shell languages
 -- My SQL follows Henry Spencer's implementation of regular expressions
 -- Look for a specific character returns 1 if the string matches the format expression
 -- format expression REGEXP pattern 
 -- match at the beginning of a strting with ^
 -- match at the end of a string with $
 -- string ending in n 
 -- ? match 0 or 1 'a' character
 -- modifying the charcter in front of it
SELECT 'Ban' REGEXP '^Ba?n';

-- How many a's are in the string ? will it match a?
SELECT 'Baan' REGEXP '^Ba?n';

-- What is this format expression representing ??
-- what about this expression what is the * being applied to 
SELECT 'pi' REGEXP '^(pi)*$';     
-- Same format string different input data 
-- will the additional p at the end of the string cause this function to fail ??             
SELECT 'pip' REGEXP '^(pi)*$'; 
 
 -- what does the empty string match??
SELECT '' REGEXP '^(pi)*$';  

-- matching mutiple copies of pi
SELECT 'pipipi' REGEXP '^(pi)*$';

-- You can also state optional matching strings 
SELECT 'apa' REGEXP 'pi|apa';

-- the brackets [] allow you to define a sequence of characters to match 
-- the {n} define the exact number of matches you expect 
-- characters to match [bcd] number of times to match character twice 
SELECT 'abcde' REGEXP 'a[bcd]{2}e';   
-- characters to match [bcd] number of times to match character three times
SELECT 'abcde' REGEXP 'a[bcd]{3}e'; 


 -- Numeric data type functions 
 use world;
 -- division 
 select name, surfacearea / population density from country;
 -- round number to a whole number 
 select  name, round(surfacearea)  from country;
 -- generate a random number for each record in the result set
 select rand(), name from country;
 -- use a seed value to recreate the numbers you generated
  select rand(15), name from country;
  
  -- can use rand to generate a random sized sample with a specific size 
  select rand(15), name from country order by rand(15) limit 10 ;
  
  -- can use rand to generate a collection of random samples 
  select * from ( 
   select rand() * 100 randnum, name from country )  randtable order by randnum limit 20 ;
   
   
 -- CASTING FUNCTIONS
 -- convert a string to a binary version 
 -- does not print as expected 
 SELECT BINARY name, name  from country;
 
 -- even though cannot print value match works for original text
 select binary name, name,
        case when binary name = name then 'Same' else 'Different'  end 
        from country;
    
-- case matters when doing a binary comparison
 select binary name, name,
        case when binary name = lower(name) then 'Same' else 'Different'  end 
        from country;       
        
        
-- conversion functions
--
--
select cast(LifeExpectancy as decimal(4,0)), LifeExpectancy from country;        
        
select convert(LifeExpectancy , decimal(4,0)), LifeExpectancy from country;              