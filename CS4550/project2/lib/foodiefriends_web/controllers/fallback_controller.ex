defmodule FoodieFriendsWeb.FallbackController do
  @moduledoc """
  Translates controller action results into valid `Plug.Conn` responses.

  See `Phoenix.Controller.action_fallback/1` for more details.
  """
  use FoodieFriendsWeb, :controller

  def call(conn, {:error, %Ecto.Changeset{} = changeset}) do
    conn
    |> put_status(:unprocessable_entity)
    |> put_view(FoodieFriendsWeb.ChangesetView)
    |> render("error.json", changeset: changeset)
  end

  def call(conn, {:error, :not_found}) do
    conn
    |> put_status(:not_found)
    |> put_view(FoodieFriendsWeb.ErrorView)
    |> render(:"404")
  end

  def call(conn, nil) do
    conn
    |> put_status(:not_found)
    |> put_view(FoodieFriendsWeb.ErrorView)
    |> render(:"404")
  end
end
