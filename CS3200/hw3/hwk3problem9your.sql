CREATE DATABASE  IF NOT EXISTS `lotr` /*!40100 DEFAULT CHARACTER SET utf8 */;
USE `lotr`;
-- MySQL dump 10.13  Distrib 5.7.17, for Win64 (x86_64)
--
-- Host: localhost    Database: lotr
-- ------------------------------------------------------
-- Server version	5.7.21-log

/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8 */;
/*!40103 SET @OLD_TIME_ZONE=@@TIME_ZONE */;
/*!40103 SET TIME_ZONE='+00:00' */;
/*!40014 SET @OLD_UNIQUE_CHECKS=@@UNIQUE_CHECKS, UNIQUE_CHECKS=0 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;

--
-- Table structure for table `lotrbooks`
--

DROP TABLE IF EXISTS `lotrbooks`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `lotrbooks` (
  `number` int(11) NOT NULL,
  `name` varchar(100) NOT NULL,
  PRIMARY KEY (`number`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `lotrbooks`
--

LOCK TABLES `lotrbooks` WRITE;
/*!40000 ALTER TABLE `lotrbooks` DISABLE KEYS */;
INSERT INTO `lotrbooks` VALUES (1,'the fellowship of the ring'),(2,'the two towers'),(3,'the return of the king');
/*!40000 ALTER TABLE `lotrbooks` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `lotrcharacters`
--

DROP TABLE IF EXISTS `lotrcharacters`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `lotrcharacters` (
  `name` varchar(50) NOT NULL,
  `species` varchar(50) NOT NULL,
  `homeland` varchar(50) NOT NULL,
  `royalty` int(11) NOT NULL,
  `fellowship` int(11) NOT NULL,
  `survive` int(11) NOT NULL,
  `alias` varchar(100) NOT NULL,
  `book_number_introduction` int(11) NOT NULL,
  PRIMARY KEY (`name`),
  KEY `lotrcharacters_fk_booknum_idx` (`book_number_introduction`),
  KEY `lotrcharacters_fk_homeland_idx` (`homeland`),
  KEY `lotrcharacters_fk_species_idx` (`species`),
  CONSTRAINT `lotrcharacters_fk_booknum` FOREIGN KEY (`book_number_introduction`) REFERENCES `lotrbooks` (`number`) ON UPDATE CASCADE,
  CONSTRAINT `lotrcharacters_fk_homeland` FOREIGN KEY (`homeland`) REFERENCES `lotrregions` (`name`) ON UPDATE CASCADE,
  CONSTRAINT `lotrcharacters_fk_species` FOREIGN KEY (`species`) REFERENCES `lotrspecies` (`Species`) ON UPDATE CASCADE
) ENGINE=InnoDB DEFAULT CHARSET=utf8;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `lotrcharacters`
--

LOCK TABLES `lotrcharacters` WRITE;
/*!40000 ALTER TABLE `lotrcharacters` DISABLE KEYS */;
INSERT INTO `lotrcharacters` VALUES ('Aragorn','human','gondor',1,1,1,'strider',1),('Eowyn','human','rohan',1,0,1,'white lady of rohan',2),('faramir','human','gondor',1,0,1,'captain of the white tower',3),('Frodo','hobbit','shire',0,1,1,'bearer of the one ring',1),('Gandalf','maiar','undying lands',0,1,1,'greybeard',1),('Gimli','dwarf','lonely mountain',0,1,1,'lockbearer',1),('Legolas','elf','mirkwood',1,1,1,'prince of the woodlands',1),('Saruman','maiar','isengard',0,0,0,'saruman the white',1),('Sauron','maiar','mordor',0,0,0,'dark lord',1);
/*!40000 ALTER TABLE `lotrcharacters` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `lotrfirstencounters`
--

DROP TABLE IF EXISTS `lotrfirstencounters`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `lotrfirstencounters` (
  `character1` varchar(50) NOT NULL,
  `character2` varchar(50) NOT NULL,
  `book` int(11) NOT NULL,
  `location` varchar(50) NOT NULL,
  PRIMARY KEY (`character1`,`character2`),
  KEY `fk_book_idx` (`book`),
  KEY `fk_location_idx` (`location`),
  CONSTRAINT `fk_book` FOREIGN KEY (`book`) REFERENCES `lotrbooks` (`number`) ON UPDATE CASCADE,
  CONSTRAINT `fk_location` FOREIGN KEY (`location`) REFERENCES `lotrregions` (`name`) ON UPDATE CASCADE
) ENGINE=InnoDB DEFAULT CHARSET=utf8;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `lotrfirstencounters`
--

LOCK TABLES `lotrfirstencounters` WRITE;
/*!40000 ALTER TABLE `lotrfirstencounters` DISABLE KEYS */;
INSERT INTO `lotrfirstencounters` VALUES ('aragorn','eowyn',2,'rohan'),('faramir','frodo',3,'mordor'),('frodo','aragorn',1,'bree'),('gandalf','frodo',1,'shire'),('saruman','aragorn',2,'isengard'),('sauron','frodo',1,'bree');
/*!40000 ALTER TABLE `lotrfirstencounters` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `lotrregions`
--

DROP TABLE IF EXISTS `lotrregions`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `lotrregions` (
  `name` varchar(50) NOT NULL,
  `major_species` varchar(50) NOT NULL,
  `description` varchar(50) NOT NULL,
  `middle_earth_location` varchar(50) NOT NULL,
  `leader` varchar(50) NOT NULL,
  PRIMARY KEY (`name`),
  KEY `lotrregions_fk_majorspecies_idx` (`major_species`),
  CONSTRAINT `lotrregions_fk_majorspecies` FOREIGN KEY (`major_species`) REFERENCES `lotrspecies` (`Species`) ON UPDATE CASCADE
) ENGINE=InnoDB DEFAULT CHARSET=utf8;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `lotrregions`
--

LOCK TABLES `lotrregions` WRITE;
/*!40000 ALTER TABLE `lotrregions` DISABLE KEYS */;
INSERT INTO `lotrregions` VALUES ('bree','human','village','north on the crossroads','none'),('gondor','human','mountainous terrain','south','Kings of Gondor'),('isengard','orc','broad plain containing the tower of Orthanc','south','Saruman'),('lonely mountain','dwarf','cave','northeast','Durin folk'),('mirkwood','elf','forested elven village','east','Thranduil'),('mordor','orc','volcanic plain','southeast','Sauron'),('rohan','human','green and fertile area','south','King of Rohan'),('shire','hobbit','grassy rolling hills','northwest','King of Arthedain'),('undying lands','Maiar','beyond middle earth','outside middle earth','none');
/*!40000 ALTER TABLE `lotrregions` ENABLE KEYS */;
UNLOCK TABLES;

--
-- Table structure for table `lotrspecies`
--

DROP TABLE IF EXISTS `lotrspecies`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `lotrspecies` (
  `Species` varchar(50) NOT NULL,
  `Description` varchar(200) NOT NULL,
  `Size` int(11) NOT NULL,
  PRIMARY KEY (`Species`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping data for table `lotrspecies`
--

LOCK TABLES `lotrspecies` WRITE;
/*!40000 ALTER TABLE `lotrspecies` DISABLE KEYS */;
INSERT INTO `lotrspecies` VALUES ('balrog','Ancient evil creatures',5),('dwarf','Dwellers of the mountains of middle earth mines for precious metals',2),('elf','Fairest and wisest species',4),('ent','Ancient beings inhabiting trees that protect the forest',6),('hobbit','Also known as halflings; mortal ancient creatures that enjoy the simple life.',1),('human','Created during the first age of middle earth; three ages after elves and other middle earth species. Mortal creatures.',3),('maiar','Holy ones with mystical powers',0),('orc','Enslaved elves that were tortured and generated a new evil species',3);
/*!40000 ALTER TABLE `lotrspecies` ENABLE KEYS */;
UNLOCK TABLES;
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed on 2018-02-05  9:24:14
