defmodule FoodieFriendsWeb.GroupsRecipeController do
  use FoodieFriendsWeb, :controller

  alias FoodieFriends.GroupsRecipes
  alias FoodieFriends.GroupsRecipes.GroupsRecipe

  action_fallback FoodieFriendsWeb.FallbackController

  def index(conn, _params) do
    groupsrecipes = GroupsRecipes.list_groupsrecipes()
    render(conn, "index.json", groupsrecipes: groupsrecipes)
  end

  def create(conn, %{"groups_recipe" => groups_recipe_params}) do
    with {:ok, %GroupsRecipe{} = groups_recipe} <- GroupsRecipes.create_groups_recipe(groups_recipe_params) do
      conn
      |> send_resp(201, Poison.encode!(%{}))
    end
  end

  def show(conn, %{"id" => id}) do
    groups_recipe = GroupsRecipes.get_groups_recipe!(id)
    render(conn, "show.json", groups_recipe: groups_recipe)
  end

  def update(conn, %{"id" => id, "groups_recipe" => groups_recipe_params}) do
    groups_recipe = GroupsRecipes.get_groups_recipe!(id)

    with {:ok, %GroupsRecipe{} = groups_recipe} <- GroupsRecipes.update_groups_recipe(groups_recipe, groups_recipe_params) do
      render(conn, "show.json", groups_recipe: groups_recipe)
    end
  end

  def delete(conn, %{"id" => id}) do
    groups_recipe = GroupsRecipes.get_groups_recipe!(id)

    with {:ok, %GroupsRecipe{}} <- GroupsRecipes.delete_groups_recipe(groups_recipe) do
      send_resp(conn, :no_content, "")
    end
  end
end
