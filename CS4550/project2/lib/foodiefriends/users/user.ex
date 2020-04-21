defmodule FoodieFriends.Users.User do
  use Ecto.Schema
  import Ecto.Changeset

  schema "users" do
    field :admin, :boolean, default: false
    field :age, :integer
    field :email, :string
    field :fname, :string
    field :gender, :string
    field :lname, :string
    field :password_hash, :string
    field :profile_url, :string
    has_many :usersgroups_id, FoodieFriends.UsersGroups.UsersGroup
    has_many :recipe_id, FoodieFriends.Recipes.Recipe

    timestamps()
  end

  @doc false
  def changeset(user, attrs) do
    user
    |> cast(attrs, [:email, :password_hash, :admin, :fname, :lname, :gender, :age, :profile_url])
    |> validate_required([:email, :password_hash])
    |> validate_format(:email, ~r/@/)
    |> unique_constraint(:email)
  end
end
