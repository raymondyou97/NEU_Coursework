/*
Raymond You
CS 3200 - Database Design
Homework 6
*/

/*
1.      Write a procedure track_character(character)  that accepts a character name and returns a result set that contains a list of 
the other characters that the provided character has encountered. The result set should contain the character’s name, the region name, 
the book name, and the name of the encountered character. (10 points)
*/

USE lotrfinal;

DROP procedure if exists track_character;
DELIMITER $$
CREATE PROCEDURE 
track_character
(    
	IN character_name varchar(255)
) 
BEGIN
SELECT character_name, temp3 as RegionName, temp2 as BookName, GROUP_CONCAT(temp4 SEPARATOR ', ') as EncounteredCharacters
FROM
(SELECT f1.character1_name as temp1, b1.title as temp2, f1.region_name as temp3, GROUP_CONCAT(f1.character2_name SEPARATOR ', ') as temp4
FROM lotr_first_encounter f1
JOIN lotr_book b1
WHERE f1.book_id = b1.book_id AND character_name = f1.character1_name AND character_name <> f1.character2_name
GROUP BY f1.character1_name
UNION ALL
SELECT f1.character2_name, b1.title, f1.region_name, GROUP_CONCAT(f1.character1_name SEPARATOR ', ')
FROM lotr_first_encounter f1
JOIN lotr_book b1
WHERE f1.book_id = b1.book_id AND character_name = f1.character2_name AND character_name <> f1.character1_name
GROUP BY f1.character2_name) final
GROUP BY temp1;

 END$$
DELIMITER ;
#Tests for characters that have encounters
CALL track_character('frodo');
CALL track_character('sauron');
#Tests for characters that don't have encounters
CALL track_character('Kathleen');
CALL track_character('BlackPanther');
 
 
 /*
2.      Write a procedure track_region(region)  that accepts a region name and returns a result set that contain the region name, the 
book name, and the number of encounters for that region. (10 points)

*/

USE lotrfinal;

DROP procedure if exists track_region;
DELIMITER $$
CREATE PROCEDURE 
track_region
(    
	IN region_name varchar(255)
) 
BEGIN
SELECT region_name as RegionName, b1.title as BookName, COUNT(*) as NumberOfEncounters
FROM lotr_first_encounter f1, lotr_book b1
WHERE b1.book_id = f1.book_id AND f1.region_name = region_name;

 END$$
DELIMITER ;

#Tests for regions that have encounters
CALL track_region('bree');
CALL track_region('rohan');
#Tests for regions that have dont' encounters
CALL track_region('Boston');
CALL track_region('China');


/*3.      Write a function named region_homeland(region). It accepts a region name and returns the number of characters that have this 
region listed as a homeland. (10 points)
*/
USE lotrfinal;

DROP FUNCTION IF EXISTS  region_homeland;
DELIMITER $$
CREATE FUNCTION region_homeland(region_name VARCHAR(255))
   RETURNS INT
 BEGIN
 DECLARE numCharacters INT;
 
 SELECT COUNT(*) into numCharacters 
 FROM lotr_character c1
 WHERE region_name = c1.homeland
 GROUP BY c1.homeland;
 RETURN (numCharacters);
 END $$
 DELIMITER ;
 
#Test for regions that are homelands for characters
SELECT region_homeland('gondor');
SELECT region_homeland('lonely mountain');
#Test for regions that aren't homelands for characters
SELECT region_homeland('Boston');
SELECT region_homeland('Africa');

/*
4.      Write a function named region_most_encounters(character) that accepts a character name and returns the name of the region where
the character has had the most encounters. (10 points) */
USE lotrfinal;

DROP FUNCTION IF EXISTS most_encounters;
DELIMITER $$
CREATE FUNCTION most_encounters(character_name VARCHAR(255))
   RETURNS VARCHAR(255)
 BEGIN
 DECLARE region_name VARCHAR(255);
 
 SELECT final.region_name into region_name
FROM (SELECT f1.region_name, COUNT(*)
 FROM lotr_first_encounter f1
 WHERE f1.character1_name = character_name
 GROUP BY f1.region_name
 UNION ALL
 SELECT f2.region_name, COUNT(*)
 FROM lotr_first_encounter f2
 WHERE f2.character2_name = character_name
 GROUP BY f2.region_name) final
 GROUP BY final.region_name
 ORDER BY COUNT(*) DESC
 LIMIT 1;
 RETURN (region_name);
 END $$
 DELIMITER ;
 
#Test that accepts a character name and returns the name of the region where the character has had the most encounters
SELECT most_encounters('gimli');
SELECT most_encounters('saruman');
SELECT most_encounters('frodo');
#Test that accepts a character name that doesn't exist and returns the name of the region where the character has had the most encounters
SELECT most_encounters('Durant');
SELECT most_encounters('Bob');

 
/*5.      Write a function named home_region_encounter(character) that accepts a character name and returns TRUE if the character has had
a first encounter in his homeland. FALSE if the character has not had a first encounter in his homeland. or NULL if the character’s homeland 
is not known. (10 points) */
 
USE lotrfinal;

DROP FUNCTION IF EXISTS home_region_encounter;
DELIMITER $$
CREATE FUNCTION home_region_encounter(character_name VARCHAR(255))
   RETURNS VARCHAR(255)
 BEGIN
 DECLARE truthValue VARCHAR(255);
 
SELECT case 
when c1.homeland IS NULL then 'NULL'
when COUNT(*) > 0 then 'TRUE'
when COUNT(*) = 0 then 'FALSE'
end as 'VALUE' into truthValue
FROM lotr_first_encounter f1, lotr_character c1
WHERE (c1.character_name = character_name AND c1.homeland IS NOT NULL) AND (c1.homeland = f1.region_name) AND
(f1.character1_name = character_name OR f1.character2_name = character_name);
 RETURN (truthValue);
 END $$
 DELIMITER ;
 
#Test that accepts a character name and returns TRUE if the character has had a first encounter in his homeland
SELECT home_region_encounter('frodo');
#Test that accepts a character name and returns FALSE if the character has not had a first encounter in his homeland
SELECT home_region_encounter('faramir');
SELECT home_region_encounter('sauron');
#Test that accepts a character name and returns NULL if the character’s homeland is not known
SELECT home_region_encounter('Durant');
SELECT home_region_encounter('Bob');


 

/*6.      Write a function named encounters_in_num_region(region_name)  that accepts a region’s name as an argument and returns the number 
of encounters for that region. (10 points) */

USE lotrfinal;

DROP FUNCTION IF EXISTS encounters_in_num_region;
DELIMITER $$
CREATE FUNCTION encounters_in_num_region(region_name VARCHAR(255))
   RETURNS INT
 BEGIN
 DECLARE numEncounters INT;
 
SELECT case 
when region_name <> f1.region_name then 0
when region_name = f1.region_name then COUNT(*)
end as 'VALUE' into numEncounters
FROM lotr_first_encounter f1
WHERE region_name = f1.region_name
GROUP BY region_name;

 RETURN (numEncounters);
 END $$
 DELIMITER ;
 
#Test that accepts a region’s name as an argument and returns the number of encounters for that region and that region exists
SELECT encounters_in_num_region('bree');
SELECT encounters_in_num_region('shire');
#Test that accepts a region’s name as an argument and returns the number of encounters for that region and that region doesn't exist
SELECT encounters_in_num_region('asdf');
SELECT encounters_in_num_region('USA');
 
/*7.      Write a procedure  named fellowship_encounters(book) that accepts a book’s name and returns the fellowship characters having 
first encounters in that book. (10 points) */

USE lotrfinal;

DROP procedure if exists fellowship_encounters;
DELIMITER $$
CREATE PROCEDURE 
fellowship_encounters
(    
	IN book_name varchar(255)
) 
BEGIN
SELECT GROUP_CONCAT(DISTINCT c1.character_name SEPARATOR ', ') as ListOfCharacters
FROM lotr_book b1, lotr_character c1, lotr_first_encounter f1
WHERE c1.fellowship = 1 AND b1.title = book_name AND b1.book_id = f1.book_id AND 
(c1.character_name = f1.character1_name OR c1.character_name = f1.character2_name);

 END$$
DELIMITER ;

#Tests that accepts a book’s name and returns the fellowship characters having first encounters in that book.
CALL fellowship_encounters('the fellowship of the ring');
CALL fellowship_encounters('the two towers');
CALL fellowship_encounters('the return of the king');
#Tests that accepts a book’s name and returns the fellowship characters not having first encounters in that book.
CALL fellowship_encounters('Harry Potter');

/*8. Modify the books table to contain a field called encounters_in_book and write a procedure called initialize_encounters_count(book)  
that accepts a book id and  initializes the field to the number of encounters that occur in that book for the current encounters table. The 
book table modification can occur outside or inside of the procedure. (10 points) */

USE lotrfinal;

ALTER TABLE lotr_book
DROP COLUMN encounters_in_book;
ALTER TABLE lotr_book
ADD encounters_in_book INT;

DROP procedure if exists encounters_in_book;
DELIMITER $$
CREATE PROCEDURE 
encounters_in_book
(    
	IN book_id INT
) 
BEGIN
DECLARE num INT;
SET @num = (SELECT COUNT(*)
FROM lotr_first_encounter f1, lotr_book b1
WHERE f1.book_id = b1.book_id AND b1.book_id = book_id
GROUP BY book_id);

UPDATE lotr_book
SET encounters_in_book = @num
WHERE lotr_book.book_id = book_id;
 END$$
DELIMITER ;

#Book table modification occuring outside the procedure
CALL encounters_in_book(1);
CALL encounters_in_book(2);
CALL encounters_in_book(3);
 
 
/*9.      Write a trigger that updates the field encounters_in_book for the book records in the lotrbook table. The field should contain 
the number of first encounters for that book.  Call the trigger firstencounters_after_insert. Insert the following records into the database.  
Insert a first encounter in Rivendell between Legolas and Frodo for book 1 . Ensure that the sencounters_in_book field is properly updated for this data. (10 points)
*/

USE lotrfinal;

DROP TRIGGER if exists firstencounters_after_insert;
DELIMITER $$

CREATE TRIGGER firstencounters_after_insert AFTER INSERT ON lotr_first_encounter
  FOR EACH ROW
  BEGIN
	CALL encounters_in_book(1);
    CALL encounters_in_book(2);
    CALL encounters_in_book(3);
END;
     
$$
DELIMITER ;



#Values Before
# book_id, title, encounters_in_book
#'1', 'the fellowship of the ring', '6'
#'2', 'the two towers', '2'
#'3', 'the return of the king', '1'
SELECT * FROM lotr_book;

#DELETE FROM lotr_first_encounter WHERE character1_name = 'Legolas' and character2_name = 'Frodo';


#Adding new encounter
INSERT INTO lotr_first_encounter
VALUES ('Legolas', 'Frodo', 1, 'Rivendell');

#Values After
# book_id, title, encounters_in_book
#'1', 'the fellowship of the ring', '1'
#'2', 'the two towers', '2'
#'3', 'the return of the king', '1'
SELECT * FROM lotr_book;

/*10.      Create and execute a prepared statement from the SQL workbench that calls home_region_encounter with the argument ‘Frodo’. Use 
a user session variable to pass the argument to the function. (5 points) */

USE lotrfinal;
SET @name := 'Frodo';
SET @query := 'SELECT home_region_encounter(@name)';
PREPARE stmt FROM @query;

EXECUTE stmt;
DEALLOCATE PREPARE stmt;

/*11.   Create and execute a prepared statement that calls encounters_in_num_region() with the argument ‘Shire’. Once again use a user session 
variable to pass the argument to the function. (5 points) */

USE lotrfinal;
SET @name := 'Shire';
SET @query := 'SELECT encounters_in_num_region(@name)';
PREPARE stmt FROM @query;

EXECUTE stmt;
DEALLOCATE PREPARE stmt;