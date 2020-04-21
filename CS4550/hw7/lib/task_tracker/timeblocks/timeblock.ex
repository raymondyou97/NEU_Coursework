defmodule TaskTracker.Timeblocks.Timeblock do
  use Ecto.Schema
  import Ecto.Changeset

  schema "timeblocks" do
    field :end, :utc_datetime
    field :start, :utc_datetime
    belongs_to :task, TaskTracker.Tasks.Task

    timestamps()
  end

  @doc false
  def changeset(timeblock, attrs) do
    finalAttrs = convertAttrs(attrs)

    timeblock
    |> cast(finalAttrs, [:start, :end, :task_id])
    |> validate_required([:start, :task_id])
  end

  def convertAttrs(attrs) do
    {:ok, startTime, 0} = DateTime.from_iso8601(attrs["start"])
    {:ok, endTime, 0} = DateTime.from_iso8601(attrs["end"])
    %{
      start: startTime,
      end: endTime,
      task_id: attrs["task_id"]
    }
  end
end
