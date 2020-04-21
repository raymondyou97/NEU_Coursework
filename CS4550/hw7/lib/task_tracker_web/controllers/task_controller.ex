defmodule TaskTrackerWeb.TaskController do
  use TaskTrackerWeb, :controller

  alias TaskTracker.Tasks
  alias TaskTracker.Tasks.Task
  alias TaskTracker.Users.User

  def index(conn, _params) do
    tasks = Tasks.list_tasks()
    render(conn, "index.html", tasks: tasks)
  end

  def new(conn, _params) do
    changeset = Tasks.change_task(%Task{})
    render(conn, "new.html", changeset: changeset)
  end

  def create(conn, %{"task" => task_params}) do
    currentUser = conn.assigns[:current_user]
    fields = User.__schema__(:fields)
    fieldModel = Map.take(currentUser, fields)
    currentUserId = fieldModel[:id]
    # map is string -> string
    task_params = Map.put(task_params, "currentUserId", Integer.to_string(currentUserId))

    case Tasks.create_task(task_params) do
      {:ok, task} ->
        conn
        |> put_flash(:info, "Task created successfully.")
        |> redirect(to: Routes.task_path(conn, :show, task))

      {:error, %Ecto.Changeset{} = changeset} ->
        render(conn, "new.html", changeset: changeset)
    end
  end

  def show(conn, %{"id" => id}) do
    task = Tasks.get_task!(id)
    user_id = get_session(conn, :user_id)
    render(conn, "show.html", task: task)
  end

  def edit(conn, %{"id" => id}) do
    task = Tasks.get_task!(id)
    changeset = Tasks.change_task(task)
    render(conn, "edit.html", task: task, changeset: changeset)
  end

  def update(conn, %{"id" => id, "task" => task_params}) do
    IO.puts("update")
    task = Tasks.get_task!(id)

    currentUser = conn.assigns[:current_user]
    fields = User.__schema__(:fields)
    fieldModel = Map.take(currentUser, fields)
    currentUserId = fieldModel[:id]
    # map is string -> string
    task_params = Map.put(task_params, "currentUserId", Integer.to_string(currentUserId))

    case Tasks.update_task(task, task_params) do
      {:ok, task} ->
        conn
        |> put_flash(:info, "Task updated successfully.")
        |> redirect(to: Routes.task_path(conn, :show, task))

      {:error, %Ecto.Changeset{} = changeset} ->
        render(conn, "edit.html", task: task, changeset: changeset)
    end
  end

  def delete(conn, %{"id" => id}) do
    task = Tasks.get_task!(id)
    {:ok, _task} = Tasks.delete_task(task)

    conn
    |> put_flash(:info, "Task deleted successfully.")
    |> redirect(to: Routes.task_path(conn, :index))
  end
end
