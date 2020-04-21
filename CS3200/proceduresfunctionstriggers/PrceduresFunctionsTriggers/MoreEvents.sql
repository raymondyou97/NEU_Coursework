DELIMITER $$
CREATE -- RUN ONCE THIS WEEK
	EVENT archive_countries_once
	ON SCHEDULE AT '2016-06-07 12:00:00' 
	DO BEGIN
		-- copy deleted posts
		INSERT INTO scratch.country_archive (id, name ) 
		SELECT id, name
		FROM scratch.country
		WHERE deleted = 1;
	END $$

CREATE 
	EVENT archive_countries_for_summer 
	ON SCHEDULE EVERY 1 WEEK 
                            STARTS '2016-06-07 12:00:00'  ENDS '2016-09-01 12:00:00'   
	DO BEGIN
		-- copy deleted posts
		INSERT INTO scratch.country_archive (id, name ) 
		SELECT id, name
		FROM scratch.country
		WHERE deleted = 1;
	END $$