defmodule FoodieFriends.Repo.Migrations.CreateUsers do
  use Ecto.Migration

  def change do
    create table(:users) do
      add :email, :string, null: false
      add :password_hash, :string, null: false
      add :admin, :boolean, default: false, null: false
      add :fname, :string
      add :lname, :string
      add :gender, :string
      add :age, :integer
      add :profile_url, :string
      timestamps()
    end

  end
end
