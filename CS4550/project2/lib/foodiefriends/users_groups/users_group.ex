defmodule FoodieFriends.UsersGroups.UsersGroup do
  use Ecto.Schema
  import Ecto.Changeset

  schema "usersgroups" do
    belongs_to :user, FoodieFriends.Users.User
    belongs_to :group, FoodieFriends.Groups.Group

    timestamps()
  end

  @doc false
  def changeset(users_group, attrs) do
    users_group
    |> cast(attrs, [:user_id, :group_id])
    |> validate_required([:user_id, :group_id])
  end
end
