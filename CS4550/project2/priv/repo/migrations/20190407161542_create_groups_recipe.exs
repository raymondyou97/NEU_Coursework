defmodule FoodieFriends.Repo.Migrations.CreateGroupsrecipes do
  use Ecto.Migration

  def change do
    create table(:groupsrecipes) do
      add :group_id, references(:groups, on_delete: :delete_all), null: false
      add :recipe_id, references(:recipes, on_delete: :delete_all), null: false

      timestamps()
    end

    create index(:groupsrecipes, [:recipe_id])
    create index(:groupsrecipes, [:group_id])
    create unique_index(:groupsrecipes, [:recipe_id, :group_id])
  end
end
