use world;
 DROP FUNCTION IF EXISTS  GetContinent ;
 DELIMITER $$
 -- CREATE A FUNCTION NAMED GetContinent 
CREATE FUNCTION GetContinent(countryname char(52))
   RETURNS VARCHAR(20)
 BEGIN
 DECLARE rcontinent VARCHAR(20);
 
 SELECT continent into rcontinent from country where name = countryname;
 RETURN (rcontinent);
 END $$ -- can use this function just like you would any MySQL built-in function
 DELIMITER ;
 
-- call the function in a SQL statement
 SELECT Name, GetContinent(Name) from country;
 
 
-- Default return value of NULL when there is no match
 SELECT Name, GetContinent('Arruba') from country;
 
 
 -- can pass values as well as fields or variable names 
  SELECT GetContinent('Aruba') as Continent from country;
 
 

 -- CREATE A FUNCTION NAMED GetCountryName 
 -- Accepts a country code as an argument 
 -- No keywords for arguments: IN, OUT, INOUT all arguments are IN 
  DROP FUNCTION IF EXISTS  GetCountryname;
DELIMITER $$
CREATE FUNCTION GetCountryname(countrycode char(3))
   RETURNS VARCHAR(52)
 BEGIN
 DECLARE rcountry VARCHAR(52);
 
 SELECT name into rcountry from country where Code = countrycode;
 RETURN (rcountry);
 END $$ -- can use this function just like you would any MySQL built-in function
 DELIMITER ;
 
 SELECT Name FROM country where Name = GetCountryName('ABW') ;
 
 -- Drop a function
 DROP FUNCTION IF EXISTS GetCountryName;