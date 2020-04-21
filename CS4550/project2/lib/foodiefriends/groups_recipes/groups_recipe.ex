defmodule FoodieFriends.GroupsRecipes.GroupsRecipe do
  use Ecto.Schema
  import Ecto.Changeset

  schema "groupsrecipes" do
    belongs_to :group, FoodieFriends.Groups.Group
    belongs_to :recipe, FoodieFriends.Recipes.Recipe

    timestamps()
  end

  @doc false
  def changeset(groups_recipe, attrs) do
    groups_recipe
    |> cast(attrs, [:group_id, :recipe_id])
    |> validate_required([:group_id, :recipe_id])
  end
end
