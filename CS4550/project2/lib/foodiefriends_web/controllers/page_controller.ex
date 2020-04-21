defmodule FoodieFriendsWeb.PageController do
  use FoodieFriendsWeb, :controller

  def index(conn, _params) do
    render(conn, "index.html")
  end
end
