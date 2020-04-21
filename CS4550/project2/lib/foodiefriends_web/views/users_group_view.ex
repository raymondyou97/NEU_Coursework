defmodule FoodieFriendsWeb.UsersGroupView do
  use FoodieFriendsWeb, :view
  alias FoodieFriendsWeb.UsersGroupView

  def render("index.json", %{usersgroups: usersgroups}) do
    %{data: render_many(usersgroups, UsersGroupView, "users_group.json")}
  end

  def render("show.json", %{users_group: users_group}) do
    %{data: render_one(users_group, UsersGroupView, "users_group.json")}
  end

  def render("users_group.json", %{users_group: users_group}) do
    %{
      id: users_group.id,
      group_id: users_group.group_id,
      user_id: users_group.user_id,
      group_name: users_group.group.name,
      group_desc: users_group.group.desc
    }
  end
end
