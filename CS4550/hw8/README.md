# TaskTrackerSPA

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

  * When user first visits the website, everything is hidden from the user except the login form, where the user will need to login or register for a new account. If the user registers for an account that already has the username taken, an error alert will popup. An error alert will also popup if the user enters a wrong username or password.
  * Once the user logs in, all the header menu options appear, such as "All Users", "All Tasks", and "My Task". The name of the menu option explicitly telling the user what will be displayed in that page.
  * The entire application is a SPA, so whenever you click on a new link, the page doesn't reload. Rather, the page is generated for you without a page reload.
  * To create a new task, you click on "New Task" in the All Tasks page and it will take you to the form. There you enter the new task attributes and submit. The new task will be created and if you click on the All Task page again your new task will be there. Error alerts will also pop up if your missing any required fields for that task.
  * To mark a task as completed, you click on edit for that task, check the checkbox for completed, and submit the changes.
