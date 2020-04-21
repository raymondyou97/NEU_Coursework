USE ex;
-- create a table without any column attributes 
CREATE TABLE vendors
(
  vendor_id     INT,
  vendor_name   VARCHAR(50)
);

-- create a table specifying specific column attributes 
-- since two NULL values are not considered the same a UNIQUE column can contain NULL values
-- in this example we do not allow NULL values in the UNIQUE columns
-- only 1 AUTO_INCREMENT field per table it must be declated as UNIQUE or the PRIMARY KEY
-- auto_increment starts at 1 but you can override that by AUTO_INCREMENT = integer
CREATE TABLE vendors
(
  vendor_id     INT            NOT NULL    UNIQUE AUTO_INCREMENT,
  vendor_name   VARCHAR(50)    NOT NULL    UNIQUE
);

-- Example of a default value for payment_total 
CREATE TABLE invoices
(
  invoice_id       INT            NOT NULL    UNIQUE,
  vendor_id        INT            NOT NULL,
  invoice_number   VARCHAR(50)    NOT NULL,
  invoice_date     DATE,
  invoice_total    DECIMAL(9,2)   NOT NULL,
  payment_total    DECIMAL(9,2)               DEFAULT 0
)
