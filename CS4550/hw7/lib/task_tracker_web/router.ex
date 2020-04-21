defmodule TaskTrackerWeb.Router do
  use TaskTrackerWeb, :router

  pipeline :browser do
    plug :accepts, ["html"]
    plug :fetch_session
    plug :fetch_flash
    plug :protect_from_forgery
    plug :put_secure_browser_headers
    plug TaskTrackerWeb.Plugs.FetchSession
  end

  pipeline :api do
    plug :accepts, ["json"]
  end

  pipeline :ajax do
    plug :accepts, ["json"]
    plug :fetch_session
    plug :fetch_flash
    plug TaskTrackerWeb.Plugs.FetchSession
  end

  scope "/", TaskTrackerWeb do
    pipe_through :browser

    get "/", PageController, :index
    get "/profile", ProfileController, :index
    get "/taskreport", TaskreportController, :index
    get "/mytasks", MytasksController, :index
    resources "/tasks", TaskController
    resources "/users", UserController
    resources "/sessions", SessionController, only: [:create, :delete], singleton: true
  end

  scope "/ajax", TaskTrackerWeb do
    pipe_through :ajax
    resources "/timeblocks", TimeblockController, except: [:new, :edit]
  end

  # Other scopes may use custom stacks.
  # scope "/api", TaskTrackerWeb do
  #   pipe_through :api
  # end
end
