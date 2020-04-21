defmodule TaskTracker.Users.User do
  use Ecto.Schema
  import Ecto.Changeset

  alias TaskTracker.Users

  schema "users" do
    field :email, :string
    field :name, :string
    has_many :tasks, TaskTracker.Tasks.Task
    belongs_to :supervisor, TaskTracker.Users.User
    has_many :underlings, TaskTracker.Users.User, foreign_key: :supervisor_id
    timestamps()
  end

  @doc false
  def changeset(user, attrs) do
    user
    |> cast(attrs, [:email, :name, :supervisor_id])
    |> validate_required([:email, :name])
    |> unique_constraint(:email)
    |> validate_format(:email, ~r/@/)
    |> validate_supervisor_id(user)
  end

  defp validate_supervisor_id(changeset, user) do
    newSupervisorId = changeset.changes[:supervisor_id]
    userId = user.id

    if changeset.valid? do
      if newSupervisorId do
        if Users.does_user_exist_by_id(newSupervisorId) do
          cond do
            newSupervisorId == userId ->
              changeset |> add_error(:supervisor_id, "You can't be the supervisor of yourself!")

            true ->
              changeset
          end
        else
          changeset |> add_error(:supervisor_id, "This supervisor user doesn't exist...")
        end
      else
        changeset
      end
    else
      changeset
    end
  end
end
