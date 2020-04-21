defmodule FoodieFriendsWeb.GroupView do
  use FoodieFriendsWeb, :view
  alias FoodieFriendsWeb.GroupView

  def render("index.json", %{groups: groups}) do
    %{data: render_many(groups, GroupView, "group.json")}
  end

  def render("show.json", %{group: group}) do
    %{data: render_one(group, GroupView, "group.json")}
  end

  def render("group.json", %{group: group}) do
    %{id: group.id,
      name: group.name,
      desc: group.desc,
      owner_id: group.owner_id}
  end
end
