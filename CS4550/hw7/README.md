# TaskTracker Part 2

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

## Design Choices for Part 2
### Managers ###

-Users can now be managers

-To be a manager, you must assign yourself some underlings. To assign yourself some underlings, you go to "All Users" to view all the users of the Task Tracker, then you click on "Edit" on the user that you want as your underling, then you enter YOUR SUPERVISOR ID in the input box for that user, and submit the changes.

-The user IDs of all Users are provided below as a table for your convenience.

-Some error handling will happen here if the input is invalid, such as if you try to assign the supervisor of yourself to be yourself and when you enter an ID of a user that doesn't exist.

### Tasks ###

-Only managers can assign tasks to their underlings now wheras before, anyone can assign tasks to anyone.

-To assign a task to an underling, click on "All Tasks", click on "New Task" at the bottom, enter the valid inputs and then enter the User ID of your underling in the box "User ID". The user IDs of all Users are provided below as a table for your convenience.

-Error handling will occur here if the inptu is invalid, such as if you try to assign the task to a user that isn't your underling and when you enter an ID of a user that doesn't exist.

### Timeblocks ###

-The 15 minute incremental time-worked on a task has been removed

-When users work on a task, they will click on "My Tasks" and a list of all your tasks will be displayed.

-To start work on a task, click on "Start Work" and the start datetime will appear.

-To end work on a task, click on "End Work" and the end datetime will appear along with the two buttons "Edit" and "Delete".

-When a task is currently in progress, the user cannot start another timeblock until the current one has ended or the user has clicked "End Work".

-If the user refreshes or leaves the page, the Start datetime will be lost and it will be as if the user has never started a time block. This was to prevent unnecessary requests to the database to store incomplete timeblocks.

-The user can also edit the timeblock and a form will appear where the user can edit the timeblock. If the user inputs an invalid format for the timeblock, an error message will appear.

### New Menu Headers Added ###

"My Profile" - Displays information about your user account, who your supervisor is, and all your underlings.

"My Task Report" - Displays information your underlings and the tasks of your underlings

"My Tasks" - Displays your user info and all your currently assigned tasks. Here you can start work and end work for these tasks.
