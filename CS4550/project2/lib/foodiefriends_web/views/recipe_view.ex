defmodule FoodieFriendsWeb.RecipeView do
  use FoodieFriendsWeb, :view
  alias FoodieFriendsWeb.RecipeView

  def render("index.json", %{recipes: recipes}) do
    %{data: render_many(recipes, RecipeView, "recipe.json")}
  end

  def render("show.json", %{recipe: recipe}) do
    %{data: render_one(recipe, RecipeView, "recipe.json")}
  end

  def render("recipe.json", %{recipe: recipe}) do
    %{id: recipe.id,
      recipe_id: recipe.recipe_id,
      rating: recipe.rating,
      image_url: recipe.image_url,
      name: recipe.name,
      display_name: recipe.display_name,
      courses: recipe.courses,
      ingredients: recipe.ingredients,
      cooktime: recipe.cooktime,
      user_id: recipe.user_id}
  end
end
