defmodule FoodieFriends.Recipes.Recipe do
  use Ecto.Schema
  import Ecto.Changeset

  schema "recipes" do
    field :cooktime, :integer
    field :courses, :string
    field :image_url, :string
    field :ingredients, :string
    field :name, :string
    field :display_name, :string
    field :rating, :integer
    field :recipe_id, :string
    belongs_to :user, FoodieFriends.Users.User

    timestamps()
  end

  @doc false
  def changeset(recipe, attrs) do
    recipe
    |> cast(attrs, [:recipe_id, :rating, :image_url, 
        :name, :courses, :ingredients, :cooktime, :user_id, :display_name])
    |> validate_required([:recipe_id, :rating, :image_url, 
        :name, :ingredients, :cooktime, :user_id, :display_name])
  end
end
