defmodule FoodieFriendsWeb.UsersGroupController do
  use FoodieFriendsWeb, :controller

  alias FoodieFriends.UsersGroups
  alias FoodieFriends.UsersGroups.UsersGroup

  action_fallback FoodieFriendsWeb.FallbackController

  def index(conn, _params) do
    usersgroups = UsersGroups.list_usersgroups()
    render(conn, "index.json", usersgroups: usersgroups)
  end

  def create(conn, %{"users_group" => users_group_params}) do
    with {:ok, %UsersGroup{} = users_group} <- UsersGroups.create_users_group(users_group_params) do
      conn
      |> send_resp(201, Poison.encode!(%{}))
    end
  end

  def show(conn, %{"id" => id}) do
    users_group = UsersGroups.get_users_group!(id)
    render(conn, "show.json", users_group: users_group)
  end

  def update(conn, %{"id" => id, "users_group" => users_group_params}) do
    users_group = UsersGroups.get_users_group!(id)

    with {:ok, %UsersGroup{} = users_group} <- UsersGroups.update_users_group(users_group, users_group_params) do
      render(conn, "show.json", users_group: users_group)
    end
  end

  def delete(conn, %{"id" => id}) do
    users_group = UsersGroups.get_users_group!(id)

    with {:ok, %UsersGroup{}} <- UsersGroups.delete_users_group(users_group) do
      send_resp(conn, :no_content, "")
    end
  end
end
