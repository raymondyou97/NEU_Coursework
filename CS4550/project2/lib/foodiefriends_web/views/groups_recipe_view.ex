defmodule FoodieFriendsWeb.GroupsRecipeView do
  use FoodieFriendsWeb, :view
  alias FoodieFriendsWeb.GroupsRecipeView

  def render("index.json", %{groupsrecipes: groupsrecipes}) do
    %{data: render_many(groupsrecipes, GroupsRecipeView, "groups_recipe.json")}
  end

  def render("show.json", %{groups_recipe: groups_recipe}) do
    %{data: render_one(groups_recipe, GroupsRecipeView, "groups_recipe.json")}
  end

  def render("groups_recipe.json", %{groups_recipe: groups_recipe}) do
    %{id: groups_recipe.id,
      group_id: groups_recipe.group_id,
      recipe_id: groups_recipe.recipe_id}
  end
end
