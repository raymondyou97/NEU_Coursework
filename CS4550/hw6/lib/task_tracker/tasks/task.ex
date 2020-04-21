defmodule TaskTracker.Tasks.Task do
  use Ecto.Schema
  import Ecto.Changeset


  schema "tasks" do
    field :description, :string
    field :time, :integer
    field :title, :string
    field :completed, :boolean, default: false
    belongs_to :user, TaskTracker.Users.User

    timestamps()
  end

  @doc false
  def changeset(task, attrs) do
    task
    |> cast(attrs, [:description, :time, :title, :completed, :user_id])
    |> validate_required([:description, :time, :title, :completed, :user_id])
  end
end
