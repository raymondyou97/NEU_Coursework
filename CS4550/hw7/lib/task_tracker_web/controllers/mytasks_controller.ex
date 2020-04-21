defmodule TaskTrackerWeb.MytasksController do
  use TaskTrackerWeb, :controller

  alias TaskTracker.Users
  alias TaskTracker.Users.User

  def index(conn, _params) do
    conn = fetch_session(conn)
    userModel = conn.assigns[:current_user]
    fields = User.__schema__(:fields)
    fieldModel = Map.take(userModel, fields)
    user = Users.get_user!(fieldModel[:id])
    tasks = TaskTracker.Tasks.list_tasks_by_user_id(user.id)
    timeblocks = TaskTracker.Timeblocks.getTimeblocksOfTasks(tasks)
    render(conn, "index.html", user: user, tasks: tasks, timeblocks: timeblocks)
  end
end
