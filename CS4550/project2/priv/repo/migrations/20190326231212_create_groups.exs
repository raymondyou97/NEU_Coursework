defmodule FoodieFriends.Repo.Migrations.CreateGroups do
  use Ecto.Migration

  def change do
    create table(:groups) do
      add :name, :string, null: false
      add :desc, :string, null: false
      add :owner_id, :integer, null: false

      timestamps()
    end
  end
end
