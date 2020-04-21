defmodule TaskTracker.Tasks.Task do
  use Ecto.Schema
  import Ecto.Changeset
  alias TaskTracker.Users

  schema "tasks" do
    field :description, :string
    field :title, :string
    field :completed, :boolean, default: false
    belongs_to :user, TaskTracker.Users.User
    has_many :timeblocks, TaskTracker.Timeblocks.Timeblock
    timestamps()
  end

  @doc false
  def changeset(task, attrs) do
    currentUserId = Map.get(attrs, "currentUserId")

    task
    |> cast(attrs, [:description, :title, :completed, :user_id])
    |> validate_required([:description, :title, :completed, :user_id])
    |> validate_isSupervisor(currentUserId)
  end

  defp validate_isSupervisor(changeset, currentUserId) do
    if changeset.valid? do
      userAssignedId = changeset.changes[:user_id]
      changes = changeset.changes

      if userAssignedId && Users.does_user_exist_by_id(userAssignedId) do
        supervisorOfUserAssignedId = Users.get_user!(userAssignedId)
        supervisorId = supervisorOfUserAssignedId.supervisor_id
        currentUserIdAsInteger = String.to_integer(currentUserId)

        if supervisorId === currentUserIdAsInteger do
          changeset
        else
          changeset
          |> add_error(
            :user_id,
            "You are not the supervisor of this user. Only supervisor of users can create tasks for that user."
          )
        end
      else
        if Map.has_key?(changes, :description) || Map.has_key?(changes, :title) ||
             Map.has_key?(changes, :completed) do
          changeset
        else
          changeset
          |> add_error(
            :user_id,
            "That user doesn't exist."
          )
        end
      end
    else
      changeset
    end
  end
end
