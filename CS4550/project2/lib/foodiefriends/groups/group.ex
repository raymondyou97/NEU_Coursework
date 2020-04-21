defmodule FoodieFriends.Groups.Group do
  use Ecto.Schema
  import Ecto.Changeset

  schema "groups" do
    field :desc, :string
    field :name, :string
    field :owner_id, :integer
    has_many :usersgroups_id, FoodieFriends.UsersGroups.UsersGroup

    timestamps()
  end

  @doc false
  def changeset(group, attrs) do
    group
    |> cast(attrs, [:name, :desc, :owner_id])
    |> validate_required([:name, :desc, :owner_id])
  end
end
