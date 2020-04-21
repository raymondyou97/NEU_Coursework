defmodule FoodieFriendsWeb.SessionController do
    use FoodieFriendsWeb, :controller

    action_fallback FoodieFriendsWeb.FallbackController

    alias FoodieFriends.Users.User
    alias FoodieFriends.Users

    def create(conn, %{"email" => email, "password" => password}) do
        with %User{} = user <- Users.get_and_auth_user(email, password) do
            resp = %{
                data: %{
                    token: Phoenix.Token.sign(FoodieFriendsWeb.Endpoint, "user_id", user.id),
                    user_id: user.id,
                    admin: user.admin,
                    email: user.email,
                    password_hash: user.password_hash,
                }
            }
            conn
            |> put_resp_header("content-type", "application/json; charset=utf-8")
            |> put_resp_cookie("user_session", Jason.encode!(resp), http_only: false)
            |> send_resp(:created, Jason.encode!(resp))
        end
    end
  end