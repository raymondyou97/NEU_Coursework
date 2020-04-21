USE sailors;

-- Nested queries with correlation – like Joins
-- SELECT names of sailors who have reserved both #103
	SELECT S.sname from Sailors S where exists 
	  (SELECT *  from Reserves R where R.bid = 103 and S.sid = R.sid) ;
      
-- Exists tests to see if the return set is empty
SELECT S.sname from Sailors S where rating > any 
   ( SELECT S2.rating from Sailors S2 where S2.sname = "yuppy");
   
   SELECT DISTINCT S.sid 
      FROM Sailors S, Boats B1, Reserves R1, Boats B2, Reserves R2 
     WHERE S.sid=R1.sid and R1.bid=B1.bid and S.sid=R2.sid and R2.bid=B2.bid 
     and (B1.color = "red" and B2.color = "green");
