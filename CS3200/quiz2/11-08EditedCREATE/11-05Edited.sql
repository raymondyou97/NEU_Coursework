-- add a new filed last_transaction_date to the table vendors
ALTER TABLE vendors
ADD last_transaction_date DATE;

-- remove a column from the table 
ALTER TABLE vendors
DROP COLUMN last_transaction_date;

-- modify the field constraint to be UNIQUE AND NOT NULL
ALTER TABLE vendors
MODIFY vendor_name VARCHAR(100) NOT NULL UNIQUE;

-- aDD A DEFAULT VALUE to an existing field
ALTER TABLE vendors
MODIFY vendor_name VARCHAR(100) NOT NULL DEFAULT 'New Vendor';

-- My SQL will not allow you to change the size of a field if that change will generate a loss of data 
ALTER TABLE vendors
MODIFY vendor_name VARCHAR(10) NOT NULL UNIQUE;

-- Examples of changing the constraints of a table

ALTER TABLE vendors
ADD PRIMARY KEY (vendor_id);

ALTER TABLE invoices
ADD CONSTRAINT invoices_fk_vendors
FOREIGN KEY (vendor_id) REFERENCES vendors (vendor_id);

ALTER TABLE vendors
DROP PRIMARY KEY;

ALTER TABLE invoices
DROP FOREIGN KEY invoices_fk_vendors;

-- rename a table 
RENAME TABLE vendors TO vendor;

-- delete all data from a table 
TRUNCATE TABLE vendor;

-- remove the table from the database
DROP TABLE vendor;

-- can drop table by specifying full table name 
DROP TABLE ex.vendor;
-- when dropping a table MySQL checks to see if other tables depend on it 
-- if there are foreign keys referencing this table you cannot drop it 
DROP TABLE vendors;