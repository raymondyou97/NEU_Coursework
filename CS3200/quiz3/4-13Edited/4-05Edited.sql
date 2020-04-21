-- example of a self join 
-- it retrieves vendors where there is another vendor also within the same city and state
-- must use table aliases to distinguish the two copies of the same table 
-- each field needs to be prefixed with the table name for disambiguation
use ap;
SELECT DISTINCT v1.vendor_name firstvendor, v1.vendor_city, -- use DISTINCT so a vendor only appears once in the result set 
    v1.vendor_state,
    v2.vendor_name secondvendor, v2.vendor_city, -- use DISTINCT so a vendor only appears once in the result set 
    v2.vendor_state
FROM vendors v1 JOIN vendors v2
    ON v1.vendor_city = v2.vendor_city AND
       v1.vendor_state = v2.vendor_state AND
       v1.vendor_name <> v2.vendor_name -- excludes same vendor matching itself 
ORDER BY v1.vendor_state, v1.vendor_city;

