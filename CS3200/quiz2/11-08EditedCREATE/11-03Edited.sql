USE ex;

-- Example of a primary key with one field 
-- each primary key is also UNIQUE, and NOT NULL and has an index associated with it
-- vendor_id  values  are managed by the DBMS
CREATE TABLE vendors
(
  vendor_id     INT            PRIMARY KEY   AUTO_INCREMENT,
  vendor_name   VARCHAR(50)    NOT NULL      UNIQUE
);

-- other syntax for defining a primary key 
-- name the constraint , specify the type of constraint
CREATE TABLE vendors
(
  vendor_id     INT            AUTO_INCREMENT,
  vendor_name   VARCHAR(50)    NOT NULL,
  CONSTRAINT vendors_pk PRIMARY KEY (vendor_id),
  CONSTRAINT vendor_name_uq UNIQUE (vendor_name)
);

-- example of a composite primary key 
-- notice the nomenclature for naming the constraints 
CREATE TABLE invoice_line_items
(
  invoice_id              INT           NOT NULL,
  invoice_sequence        INT           NOT NULL,
  line_item_description   VARCHAR(100)  NOT NULL,
  CONSTRAINT line_items_pk PRIMARY KEY (invoice_id, invoice_sequence)
)