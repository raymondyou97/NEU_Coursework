USE scratch;
show events;
SET GLOBAL event_scheduler = OFF;
show processlist;
SET GLOBAL event_scheduler = ON;
show processlist;

create schema if not exists scratch;
use scratch;
drop table if exists country; 
create table country (code char(3), name char(35), deleted integer);
insert into country (code, name, deleted ) 
VALUES 
 ('ESH', 'Western Sahara', 1),
('GAB', 'Gabon', 1);
drop table if exists archive_countries; 
create table archive_countries (code char(3), name char(35), archive_d timestamp);

select * from mysql.event;
-- create a simple event that archives deleted records 
-- from the active tables 
DELIMITER $$
CREATE 
	EVENT archive_countries 
	ON SCHEDULE EVERY 1 WEEK STARTS '2016-06-07 12:00:00' 
	DO BEGIN
	
		-- copy deleted posts
		INSERT INTO scratch.country_archive (id, name ) 
		SELECT id, name
		FROM scratch.country
		WHERE deleted = 1;
	END $$

DELIMITER ;
/* Class work change the EVENT to run:
                 a. only run once today
                 b. run every week until 2016-09-01*/
                 
-- table for events
select * from mysql.event;

-- delete the event 
drop event archive_countries;