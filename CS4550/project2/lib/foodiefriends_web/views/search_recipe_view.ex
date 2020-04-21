defmodule FoodieFriendsWeb.SearchRecipeView do
    use FoodieFriendsWeb, :view
  
    def render("index.json", recipe) do
      %{data: %{recipe: recipe}}
    end
  end