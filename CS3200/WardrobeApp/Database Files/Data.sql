USE wardrobeapp;

#Inserting Users
#Password with MD5 hashing
INSERT INTO user (FName, LName, Age, Gender, EmailAddress, Username, Password) VALUES
('Joseph', 'Aoun', 60, 'Male', 'j.aoun@husky.neu.edu', 'josephaoun', '5f80ab70a113dddb87d55f28ba82095c');

INSERT INTO user (FName, LName, Age, Gender, EmailAddress, Username, Password) VALUES
('Kathleen', 'Durant', 35, 'Female', 'k.durant@husky.neu.edu', 'kathleendurant', '5f80ab70a113dddb87d55f28ba82095c');

INSERT INTO user (FName, LName, Age, Gender, EmailAddress, Username, Password) VALUES
('Raymond', 'You', 420, 'Male', 'you.r@husky.neu.edu', 'raymondyou', '5f80ab70a113dddb87d55f28ba82095c');

INSERT INTO user (FName, LName, Age, Gender, EmailAddress, Username, Password) VALUES
('Elizabeth', 'Cho', 69, 'Female', 'cho.e@husky.neu.edu', 'elizabethcho', '5f80ab70a113dddb87d55f28ba82095c');

#Inserting Outfits
INSERT INTO Outfit (UserID, OutfitDescription) VALUES
(3, "Spring");
INSERT INTO Outfit (UserID, OutfitDescription) VALUES
(3, "Winter");
INSERT INTO Outfit (UserID, OutfitDescription) VALUES
(3, "Rave Outfit");
INSERT INTO Outfit (UserID, OutfitDescription) VALUES
(3, "Date Outfit");
INSERT INTO Outfit (UserID, OutfitDescription) VALUES
(3, "Interview Attire");

#Inserting Types
INSERT INTO ArticleType (Type, TypeDescription) VALUES ('short-sleeve', 'a short-sleeve article');
INSERT INTO ArticleType (Type, TypeDescription) VALUES ('long-sleeve', 'a long-sleeve article');
INSERT INTO ArticleType (Type, TypeDescription) VALUES ('hoodie', 'a hoodie article');
INSERT INTO ArticleType (Type, TypeDescription) VALUES ('dress', 'a dress article');

#Inserting Articles
INSERT INTO outfitarticle (articletype, size, color, brand, material, price, userid, articledescription, datepurchased) VALUES
(1, 'small', 'yellow', 'Uniqlo', 'cotton', 100, 3, 'for dates', STR_TO_DATE('1-01-2012', '%d-%m-%Y'));
INSERT INTO outfitarticle (articletype, size, color, brand, material, price, userid, articledescription, datepurchased) VALUES
(1, 'small', 'yellow', 'Uniqlo', 'cotton', 100, 3, 'bum friday', STR_TO_DATE('1-01-2012', '%d-%m-%Y'));
INSERT INTO outfitarticle (articletype, size, color, brand, material, price, userid, articledescription, datepurchased) VALUES
(2, 'medium', 'yellow', 'Uniqlo', 'nylon', 123, 3, 'casual', STR_TO_DATE('1-03-2015', '%d-%m-%Y'));
INSERT INTO outfitarticle (articletype, size, color, brand, material, price, userid, articledescription, datepurchased) VALUES
(3, 'large', 'green', 'Express', 'cotton', 331, 3, 'match with green', STR_TO_DATE('2-05-2017', '%d-%m-%Y'));
INSERT INTO outfitarticle (articletype, size, color, brand, material, price, userid, articledescription, datepurchased) VALUES
(3, 'large', 'green', 'Express', 'cotton', 123, 3, 'lit', STR_TO_DATE('2-05-2017', '%d-%m-%Y'));
INSERT INTO outfitarticle (articletype, size, color, brand, material, price, userid, articledescription, datepurchased) VALUES
(3, 'large', 'green', 'Express', 'cotton', 420, 3, 'swaggity poppin', STR_TO_DATE('2-05-2017', '%d-%m-%Y'));
INSERT INTO outfitarticle (articletype, size, color, brand, material, price, userid, articledescription, datepurchased) VALUES
(4, 'x-large', 'orange', 'Nike', 'polyester', 69, 3, 'gym top', STR_TO_DATE('2-05-2017', '%d-%m-%Y'));

#Inserting into outfits-articles
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (1, 1);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (1, 2);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (1, 3);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (1, 4);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (1, 5);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (1, 6);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (1, 7);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (2, 1);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (3, 4);
INSERT INTO outfittoarticle (OutfitID, ArticleID) VALUES (3, 5);


