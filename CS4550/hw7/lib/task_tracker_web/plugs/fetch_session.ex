defmodule TaskTrackerWeb.Plugs.FetchSession do
  import Plug.Conn

  def init(args), do: args

  def call(conn, _args) do
    user = TaskTracker.Users.get_user(get_session(conn, :user_id) || -1)
    users = TaskTracker.Users.list_users()

    if user do
      assign(conn, :current_user, user)
      |> assign(:users, users)
    else
      assign(conn, :current_user, nil)
      |> assign(:users, users)
    end
  end
end
