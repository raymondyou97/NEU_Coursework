/*
Raymond You
CS 3200 Database Design
Professor Durant



1) How many databases are created by the script?
-Three databases are created by the script (om, ex, ap)

2) List the database names and the tables created for each database.
Database - ap
Tables - general_ledger_accounts, invoice_archive, invoice_line_items, invoices, iterms, vendor_contacts, vendors

Database - ex
Tables - active_invoices, color_sample, customers, date_sample, 
departments, employees, float_sample, null_sample, paid_invoices, projects, string_sample

Database - om
Tables - customers, items, order_details, orders

3) How many records does the script insert into the om.order_details table?
-The script inserts 68 records into the om.order_details table.

4) What is the primary key for the om.customers table?
-The primary key for the om.customers table is customer_id.

5) Select all fields from the table orders
-below

6) Select the fields title and artist from the om.items table
-below
*/

SELECT * FROM orders;

SELECT title, artist FROM items;