USE ex;

-- Foreign key constraint at the column level 
-- these constraints enfored for the InnoDB database engine
-- the default database engine
-- when creating tables you must create the tables without the foreign keys first
-- other create table commands can then refer to these tables during there creation
-- when dropping tables you must drop the referencing table (with the foreign key)  before dropping the referenced table
CREATE TABLE invoices
(
  invoice_id       INT            PRIMARY KEY,
  vendor_id        INT            REFERENCES vendors (vendor_id),
  invoice_number   VARCHAR(50)    NOT NULL    UNIQUE
);

-- foreign key constraint at the table level 
CREATE TABLE invoices
(
  invoice_id       INT           PRIMARY KEY,
  vendor_id        INT           NOT NULL,
  invoice_number   VARCHAR(50)   NOT NULL    UNIQUE,
  CONSTRAINT invoices_fk_vendors
    FOREIGN KEY (vendor_id) REFERENCES vendors (vendor_id)
)