defmodule FoodieFriends.Repo.Migrations.CreateUsersgroups do
  use Ecto.Migration

  def change do
    create table(:usersgroups) do
      add :user_id, references(:users, on_delete: :delete_all), null: false
      add :group_id, references(:groups, on_delete: :delete_all), null: false

      timestamps()
    end

    create index(:usersgroups, [:user_id])
    create index(:usersgroups, [:group_id])
  end
end
