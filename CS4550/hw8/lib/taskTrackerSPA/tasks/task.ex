defmodule TaskTrackerSPA.Tasks.Task do
  use Ecto.Schema
  import Ecto.Changeset

  schema "tasks" do
    field :completed, :boolean, default: false
    field :desc, :string
    field :time, :integer
    field :title, :string
    belongs_to :user, TaskTrackerSPA.Users.User

    timestamps()
  end

  @doc false
  def changeset(task, attrs) do
    task
    |> cast(attrs, [:completed, :desc, :time, :title, :user_id])
    |> validate_required([:completed, :desc, :time, :title, :user_id])
  end
end
