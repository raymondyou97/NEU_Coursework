defmodule BattleshipsWeb.Router do
  use BattleshipsWeb, :router

  pipeline :browser do
    plug :accepts, ["html"]
    plug :fetch_session
    plug :fetch_flash
    plug :protect_from_forgery
    plug :put_secure_browser_headers
  end

  pipeline :api do
    plug :accepts, ["json"]
  end

  scope "/", BattleshipsWeb do
    pipe_through :browser

    get "/", PageController, :index
    post "/join", PageController, :join
    get "/game/:name", PageController, :game
  end

  # Other scopes may use custom stacks.
  # scope "/api", BattleshipsWeb do
  #   pipe_through :api
  # end
end
