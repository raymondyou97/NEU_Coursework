defmodule TaskTrackerSPAWeb.Router do
  use TaskTrackerSPAWeb, :router

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

  scope "/", TaskTrackerSPAWeb do
    pipe_through :browser

    get "/", PageController, :index

    #keep or not, leave for now...
    get "/users", PageController, :index
    get "/tasks", PageController, :index
    get "/tasks/new", PageController, :index
  end

  scope "/api/v1", TaskTrackerSPAWeb do
    pipe_through :api
    resources "/users", UserController, except: [:new, :edit]
    resources "/tasks", TaskController, except: [:new, :edit]
    resources "/sessions", SessionController, only: [:create]

    post "/token", TokenController, :create
  end
end
