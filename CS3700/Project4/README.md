# Project 4

- Web Crawler
- Team Name: PythonCats
- Team Members: Raymond You, Oliver Zheng

## High-level Approach

First, we understood how fakebook worked as a whole in terms of requests made, what those requests had, header information, etc and disected fakebook before starting the crawler implementation. Next, we made a simple socket connection that is just a regular GET request on the homepage of fakebook. Once that was working, we retrieved the CSRF value from the initial page load. Once we had the CSRF value, we did a socket POST request to login with the provided username and password. Once that was working, we pulled the session id from the response returned back as we will need that for the actual crawling part. Finally, we used the CSRF value and session ID to make a cookie that allows our crawler to continuously crawl fakebook until they find all 5 secret flags.

## Challenges Faced

One of the challenges faced was our program was running too slow and we couldn't tell if it just stopped working or it was taking too long. We added threading through the built-in Python thread library and that seemed to fix things, but ran into race conditions if two threads find the same flag and put the same flag twice into our list. We fixed this by changing it into sets.

Another challenge was we had trouble making a POST request as we kept getting a 404. It was a simple spacing issue and formatting issue in the request header that was annoying to debug.

## Overview of Testing

We mainly tested as usual by printing statements each time we made a incremental checkpoint in this project. Everytime we made a change, we made sure that the print statements were printing the correct output.
