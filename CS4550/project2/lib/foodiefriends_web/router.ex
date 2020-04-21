defmodule FoodieFriendsWeb.Router do
  use FoodieFriendsWeb, :router

  # mix phx.routes FoodieFriendsWeb.Router

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

  scope "/", FoodieFriendsWeb do
    pipe_through :browser

    get "/", PageController, :index

    get "/myprofile", PageController, :index
    get "/myrecipes", PageController, :index
    get "/mygroups", PageController, :index
    get "/users", PageController, :index
    get "/groups", PageController, :index
    get "/usersgroups", PageController, :index
    get "/groupsrecipes", PageController, :index
    get "/allgroups", PageController, :index
  end

  scope "/api/v1", FoodieFriendsWeb do
    pipe_through :api

    resources "/sessions", SessionController, only: [:create]
    resources "/users", UserController, except: [:new, :edit]
    resources "/groups", GroupController, except: [:new, :edit]
    resources "/usersgroups", UsersGroupController, except: [:new, :edit]
    resources "/recipes", RecipeController, except: [:new, :edit]
    resources "/messages", MessageController, except: [:new, :edit]
    resources "/images", ImageController, only: [:create]
    #exteral api route
    resources "/searchrecipe", SearchRecipeController, except: [:new, :edit]
    resources "/groupsrecipes", GroupsRecipeController, except: [:new, :edit]
  end
end
