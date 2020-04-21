defmodule FoodieFriends.Repo.Migrations.CreateMessages do
  use Ecto.Migration

  def change do
    create table(:messages) do
      add :msg, :string, null: false
      add :user_id, references(:users, on_delete: :delete_all), null: false
      add :group_id, references(:groups, on_delete: :delete_all), null: false

      timestamps()
    end

    create index(:messages, [:user_id])
    create index(:messages, [:group_id])
  end
end
