#Raymond You
#CS3200 - Database Design
#Professor Kathleen Durant
#HW 5


#4. Generate a list of players who have scored more than 10 goals. The result should contain the
#   player’s name, team and number of goals.
SELECT Name, Club, GoalsScored
FROM players
WHERE GoalsScored > 10
ORDER BY GoalsScored ASC;


#5. Generate a list of managers, teams and the number of goals for each team for the season. The
#   result should contain the manager’s name, the team name, and the number of goals.
SELECT Name as ManagerName, Team as TeamName, TotalGoals FROM managers JOIN (SELECT Club, SUM(GoalsScored) as TotalGoals
FROM players
GROUP BY Club) as Table1
WHERE managers.Team = Table1.Club;


#6. Determine the most popular nationality for the players. The result is a single value.
SELECT Nationality, COUNT(*) as MostPopularNationality
FROM players
GROUP BY Nationality
ORDER BY MostPopularNationality DESC
LIMIT 1;

#7. Determine the number of yellows cards given per team. The result should contain the team name
#   and the number of card.
SELECT Club, COUNT(YellowCards) as NumberOfYellowCards
FROM players
GROUP BY Club;

#8. Determine the top 5 goalkeepers ranked by clean sheets. The result should contain the player’s
#	name, the team’s name and the count of the clean sheets. The result should be ordered in
#	descending order by the count of clean sheets.
SELECT Name, Club, CleanSheets
FROM players
WHERE Position = "Goalkeeper"
ORDER BY CleanSheets DESC
LIMIT 5;

#9. Determine the number of minutes played for each of the player. The result should consist of a
#	player’s name and the number of minutes.
SELECT Name, MinutesPlayed
FROM Players;

#10. Generate a list consisting of a manager’s name, a team’s name and its home stadium, as well as
#	 the total number of red cards for issued to the player’s of the team.
SELECT managers.Name as ManagerName, stadiums.Team as TeamName, 
stadiums.Venue as HomeStadium, stadiums.NumberOfRedCards FROM managers JOIN 
	(SELECT Team, NumberOfRedCards, Venue FROM stadiums JOIN
		(SELECT Club, COUNT(RedCards) as NumberOfRedCards
			FROM players
			GROUP BY Club) as players
			WHERE stadiums.Team = players.Club) as stadiums
							WHERE managers.Team = stadiums.Team;
                            
#11. Determine the top 5 forwards ranked by minutes played. The result should consist of the player’s
#	 name, the team’s name and the total minutes played.
SELECT Name, Club, MinutesPlayed
FROM players
WHERE Position = "Forward"
ORDER BY MinutesPlayed DESC
LIMIT 5;

#12. Are there any players from Ireland (either Northern or Southern) with more than 10 goals?
SELECT *
FROM players
WHERE (Nationality = "Ireland" or Nationality = "Northern Ireland") and GoalsScored > 10;

#13. What is the average playing time for the players? The result is a single number.
SELECT ROUND(avg(MinutesPlayed), 2) as AveragePlayingTimeForThePlayers
FROM players;

#14. What is the average playing time for each of the positions. The result should contain the position
#	 and the average playing time for that position.
SELECT Position, ROUND(avg(MinutesPlayed), 2) as AveragePlayingTime
FROM players
GROUP BY Position;

#15. Determine the players with above average playing time. The result should contain the player’s
#	 name, the team’s name and the player’s playing time.
SELECT players.Name, players.MinutesPlayed FROM players 
JOIN (SELECT ROUND(avg(MinutesPlayed), 2) as AveragePlayingTime
FROM players) as Averages
WHERE players.MinutesPlayed > Averages.AveragePlayingTime;

