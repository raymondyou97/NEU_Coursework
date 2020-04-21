defmodule FoodieFriends.Repo.Migrations.CreateRecipes do
  use Ecto.Migration

  def change do
    create table(:recipes) do
      add :recipe_id, :string, null: false
      add :rating, :integer
      add :image_url, :string
      add :name, :string, null: false
      add :display_name, :string
      add :courses, :string
      add :ingredients, :string
      add :cooktime, :integer
      add :user_id, references(:users, on_delete: :delete_all), null: false

      timestamps()
    end

    create index(:recipes, [:user_id])
  end
end
