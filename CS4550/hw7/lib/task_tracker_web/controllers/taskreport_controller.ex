defmodule TaskTrackerWeb.TaskreportController do
  use TaskTrackerWeb, :controller

  alias TaskTracker.Users
  alias TaskTracker.Users.User
  alias TaskTracker.Tasks

  def index(conn, _params) do
    conn = fetch_session(conn)
    userModel = conn.assigns[:current_user]
    fields = User.__schema__(:fields)
    fieldModel = Map.take(userModel, fields)
    currentUser = Users.get_user!(fieldModel[:id])
    underlings = Users.get_underlings(fieldModel[:id])
    underlingsTasks = Tasks.get_all_tasks_of_underlings(underlings)

    render(conn, "index.html",
      currentUser: currentUser,
      underlings: underlings,
      underlingsTasks: underlingsTasks
    )
  end
end
