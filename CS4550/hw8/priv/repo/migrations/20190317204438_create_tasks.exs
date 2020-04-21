defmodule TaskTrackerSPA.Repo.Migrations.CreateTasks do
  use Ecto.Migration

  def change do
    create table(:tasks) do
      add :completed, :boolean, default: false, null: false
      add :desc, :string, null: false
      add :time, :integer, default: 0, null: false
      add :title, :string, null: false
      add :user_id, references(:users, on_delete: :delete_all)

      timestamps()
    end

    create index(:tasks, [:user_id])
  end
end
