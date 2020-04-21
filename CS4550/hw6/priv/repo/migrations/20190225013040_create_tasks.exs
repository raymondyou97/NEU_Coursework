defmodule TaskTracker.Repo.Migrations.CreateTasks do
  use Ecto.Migration

  def change do
    create table(:tasks) do
      add :description, :string
      add :time, :integer

      timestamps()
    end

  end
end
