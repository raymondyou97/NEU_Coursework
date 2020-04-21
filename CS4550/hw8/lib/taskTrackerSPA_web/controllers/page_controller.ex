defmodule TaskTrackerSPAWeb.PageController do
  use TaskTrackerSPAWeb, :controller

  alias TaskTrackerSPA.Tasks
  def index(conn, _params) do
    allTasks = Tasks.list_tasks()
    |> Enum.map(&(Map.take(&1, [:completed, :desc, :time, :title, :id])))
    render(conn, "index.html", tasks: allTasks)
  end
end
