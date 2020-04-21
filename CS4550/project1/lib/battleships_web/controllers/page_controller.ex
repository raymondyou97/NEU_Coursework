defmodule BattleshipsWeb.PageController do
  use BattleshipsWeb, :controller

  def index(conn, _params) do
    render conn, "index.html"
  end

  # Taken from https://github.com/NatTuck/hangman/blob/multiplayer/lib/hangman_web/controllers/page_controller.ex
  def join(conn, %{"join" => %{"user" => user, "name" => name}}) do
    conn
    |> put_session(:user, user)
    |> redirect(to: "/game/#{name}")
  end

  def game(conn, params) do
    user = get_session(conn, :user)
    if user do
      render conn, "game.html", name: params["name"], user: user
    else
      conn
      |> put_flash(:error, "Must pick a username")
      |> redirect(to: "/")
    end
  end
end