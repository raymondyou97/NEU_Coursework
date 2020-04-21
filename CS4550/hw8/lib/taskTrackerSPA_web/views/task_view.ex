defmodule TaskTrackerSPAWeb.TaskView do
  use TaskTrackerSPAWeb, :view
  alias TaskTrackerSPAWeb.TaskView

  def render("index.json", %{tasks: tasks}) do
    %{data: render_many(tasks, TaskView, "task.json")}
  end

  def render("show.json", %{task: task}) do
    %{data: render_one(task, TaskView, "task.json")}
  end

  def render("task.json", %{task: task}) do
    %{
      id: task.id,
      completed: task.completed,
      desc: task.desc,
      time: task.time,
      title: task.title,
      user_id: task.user_id,
    }
  end
end
