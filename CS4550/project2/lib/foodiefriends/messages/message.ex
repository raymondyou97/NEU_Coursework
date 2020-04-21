defmodule FoodieFriends.Messages.Message do
  use Ecto.Schema
  import Ecto.Changeset

  schema "messages" do
    field :msg, :string
    belongs_to :user, FoodieFriends.Users.User
    belongs_to :group, FoodieFriends.Groups.Group

    timestamps()
  end

  @doc false
  def changeset(message, attrs) do
    message
    |> cast(attrs, [:msg, :user_id, :group_id])
    |> validate_required([:msg, :user_id, :group_id])
  end
end
