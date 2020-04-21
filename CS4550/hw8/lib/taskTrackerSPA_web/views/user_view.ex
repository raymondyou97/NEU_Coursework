defmodule TaskTrackerSPAWeb.UserView do
  use TaskTrackerSPAWeb, :view
  alias TaskTrackerSPAWeb.UserView

  def render("index.json", %{users: users}) do
    %{data: render_many(users, UserView, "user.json")}
  end

  def render("show.json", %{user: user}) do
    %{data: render_one(user, UserView, "user.json")}
  end

  def render("user.json", %{user: user}) do
    %{id: user.id,
      email: user.email,
      password_hash: user.password_hash,
      admin: user.admin}
  end
end
