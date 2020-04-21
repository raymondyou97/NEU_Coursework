-- AN index speeds up joins and searches by providing a way for  the DBMS to go directly
-- to a row having a specific value rather than having to search through all the rows

-- by default MySQL creates indexes for the primary and foreign keys, unique keys of a table
-- you can also specify other fields you want to create an index for frequently used fields in search conditions
-- however there is a price to pay for indexes , they are a data store that needs to be updated when the data is updated

-- to create an index name the index reference the table and the field
CREATE INDEX invoices_invoice_date_ix
  ON invoices (invoice_date);
  
-- index that is composed of 2 fields the order of the fields specify the order for the index  
CREATE INDEX invoices_vendor_id_invoice_number_ix
  ON invoices (vendor_id, invoice_number);

-- you can specify that the index will have unique values 
CREATE UNIQUE INDEX vendors_vendor_phone_ix
  ON vendors (vendor_phone);

-- can specify if you want the dat sorted in descending order , default is ascending order   
CREATE INDEX invoices_invoice_total_ix
  ON invoices (invoice_total DESC);
 
 -- can remove an index with the DROP command 
DROP INDEX vendors_vendor_phone_ix ON vendors;