defmodule TaskTracker.Repo.Migrations.AddUserToTasks do
  use Ecto.Migration

  def change do
    alter table(:tasks) do
      add :title, :string, null: false
      add :user_id, references(:users, on_delete: :delete_all), null: false
      add :completed, :boolean, default: false, null: false
    end
  end
end
