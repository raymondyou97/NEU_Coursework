# TaskTracker

To start your Phoenix server:

  * Install dependencies with `mix deps.get`
  * Create and migrate your database with `mix ecto.setup`
  * Install Node.js dependencies with `cd assets && npm install`
  * Start Phoenix endpoint with `mix phx.server`

Now you can visit [`localhost:4000`](http://localhost:4000) from your browser.

Ready to run in production? Please [check our deployment guides](https://hexdocs.pm/phoenix/deployment.html).

## Learn more

  * Official website: http://www.phoenixframework.org/
  * Guides: https://hexdocs.pm/phoenix/overview.html
  * Docs: https://hexdocs.pm/phoenix
  * Mailing list: http://groups.google.com/group/phoenix-talk
  * Source: https://github.com/phoenixframework/phoenix

## Design Choices
The two many models/entities in this task tracker application are users and tasks.

*Users*

-Each user has an email address field and a name field and a tasks field

-The user has a 0..* relationship with the tasks meaning the user can have 0 to many tasks

-When a user registers, that user is required to enter an email address and a name

-The email address will be how the user logs in, after registering

-Once the user registers an account, the user can view the account or go back

*Tasks*

-Each task has the fields description, time, title, completed, and user

-Description would be a description of the task

-Time would be the time worked on for a task in specific 15 minute increments

-Title would be the title of the task

-Completed would be if the user has completed the task or not

-User would be the owner of the task where each task can only be owned by ONE user

-To assign the task to a user, you must enter the user ID of that user (all the users are displayed under this field for convenience)

*General*

-Once the user register/has an account and logs in, the user is redirected back to the home page with the list of tasks currently assigned to that user

-The user can also view all the other users and tasks in the navigation menu.
