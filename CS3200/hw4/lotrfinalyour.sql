/*
Raymond You
CS 3200 Database Design
Professor Durant
HW4



1.      (10 points) Review the given schema and compare it to your original Lord of the Rings schema design. Identify the differences 
between the downloaded schema and your original schema. For each identified difference state whether you believe the identified change: 
improves/decreases the readability of the schema, improves/decreases the mechanics of the data integrity, or is a variation of the same solution.
 
 Difference #1
 Mine: I have all of these table columns as NOT NULL. lotr_book: title, lotr_character: species, homeland, royalthy, 
 fellowship, survive, alias, book_number_introduction, lotr_first_encounter: book_id, region_name, lotr_region: major_species, 
 description, middle_earth_location, leader, lotr_species: description, size
 Given: The table columns above are nullable here.
 Reason: The given change improved the mechanics of the data integrity as you shouldn't need all these columns filled in for some of these tables
 
 Difference #2
 Mine: Varchar(length) length is various values for example, name would be varchar(50) while description would be varchar(200)
 Given: All the varchar(length) has length 255.
 Reason: Is a variation of the same solution. Just increasing the maximum varchar length though realistically I dont't some 
 columns such as name and homeland need 255 lengths.
 
 Difference #3
 Mine: In table lotrcharacters, there is CONSTRAINT `lotrcharacters_fk_booknum` FOREIGN KEY (`book_number_introduction`) 
 REFERENCES `lotrbooks` (`number`) ON UPDATE CASCADE
 Given: Foreign key of above is not there
 Reason: The change in mine improves the mechanics of the data integrity as book number should reference the table lotrbooks number column.
 
 Difference #4
 Mine: Two foreign keys below are not in my model.
 Given: 
 CONSTRAINT `encounter_fk1` FOREIGN KEY (`character1_name`) REFERENCES `lotr_character` (`character_name`) ON DELETE CASCADE ON UPDATE CASCADE,
 CONSTRAINT `encounter_fk2` FOREIGN KEY (`character2_name`) REFERENCES `lotr_character` (`character_name`) ON DELETE CASCADE ON UPDATE CASCADE,
 Reason: The given change improves the mchanics of the data integrity as characters should be connected or have a foreign 
 key to table characters, character_name.
 
Write SQL queries that answer the following questions:
*/

#2.      (10 points) For each character, count the number of encounters documented within the database.
SELECT   CharacterName, COUNT(*) AS Encounters
FROM     (SELECT character1_name AS CharacterName
          FROM   lotr_first_encounter
          UNION ALL
          SELECT character2_name AS CharacterName
          FROM   lotr_first_encounter) x
GROUP BY CharacterName
ORDER BY Encounters DESC;


#3.      (10 points) Count the number of regions each character has visited (as documented in the database).
SELECT CharacterName, COUNT(DISTINCT region_name) AS numberOfRegionsVisited 
FROM (SELECT character1_name AS CharacterName, region_name
          FROM   lotr_first_encounter
          UNION ALL
          SELECT character2_name AS CharacterName, region_name
          FROM   lotr_first_encounter) x
GROUP BY CharacterName
ORDER BY numberOfRegionsVisited DESC;


#4.      (10 points) Count the number of regions whose majority species is ‘hobbit’.
SELECT COUNT(DISTINCT major_species) AS numHobbitMajorSpecies
FROM lotr_region WHERE major_species = "hobbit";

#5.      (10 points) What region has been documented as having the most number of first encounters?
SELECT region_name, COUNT(region_name) AS regionOccurance
FROM     lotr_first_encounter
GROUP BY region_name
ORDER BY regionOccurance DESC
LIMIT    1;

#6.      (10 points) What region has been visited by all characters?
SELECT region_name AS VisitedByAll FROM lotr_first_encounter 
INNER JOIN lotr_character ON lotr_first_encounter.character1_name = lotr_character.character_name
GROUP BY region_name HAVING COUNT(DISTINCT lotr_first_encounter.character1_name) = (SELECT COUNT(character_name) FROM lotr_character);

#7.      (5 points) Make a separate table from the lotrfirstencounters table – where the records are for the first book. 
#					Name the new table book1encounters.
DROP TABLE IF EXISTS book1encounters;
CREATE TABLE book1encounters AS (SELECT * FROM lotr_first_encounter WHERE book_id = 1);

#8.      (10 points) Which book (book name) does ‘Frodo’ encounter ‘Faramir’?
SELECT title as BookName from lotr_book
INNER JOIN lotr_first_encounter ON lotr_first_encounter.book_id = lotr_book.book_id
WHERE character1_name = "faramir" AND character2_name = "frodo" or
character1_name = "frodo" AND character2_name = "faramir";

#9.      (5 points) For each Middle Earth region, create an aggregated field that contains a list of character names that have 
#					it as his homeland. The result set should contain the region name and the grouped character names. 
#					Do not duplicate names within the grouped list of character names.
SELECT middle_earth_location as MiddleEarthLocation, GROUP_CONCAT(DISTINCT character_name) AS CharacterList FROM lotr_region
INNER JOIN lotr_character WHERE lotr_region.region_name = lotr_character.homeland GROUP BY MiddleEarthLocation;

#10.   (5 points) Which is the largest species?
SELECT species_name as SpeciesName, size AS largestSize
FROM     lotr_species
GROUP BY size
ORDER BY largestSize DESC
Limit 1;

#11.   (5 points) How many characters are “human”?
SELECT species as Human, COUNT(species) AS AmountofHumans
FROM     lotr_character
WHERE lotr_character.species = "human"
GROUP BY species;

#12.   (5 points) Make a separate table from the first encounter table – where the tuples are the first encounters 
#				  between hobbits and humans. Name the table HumanHobbitsFirstEncounters.
DROP TABLE IF EXISTS HumanHobbitsFirstEncounters;
CREATE TABLE HumanHobbitsFirstEncounters as
(SELECT character1_name, character2_name, book_id, region_name FROM lotr_first_encounter f1 JOIN lotr_character c1
 JOIN lotr_character c2 WHERE f1.character1_name = c1.character_name and f1.character2_name = c2.character_name
						  and (c1.species = "human" and c2.species = "hobbit" or c1.species = "hobbit" and c2.species = "human")); 

#13.   (5 points) List the names of the characters that have “gondor” listed as their home land.
SELECT character_name as GondorCharacters FROM lotr_character WHERE homeland = "gondor";