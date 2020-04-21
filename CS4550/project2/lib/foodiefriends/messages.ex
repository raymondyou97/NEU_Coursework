defmodule FoodieFriends.Messages do
  @moduledoc """
  The Messages context.
  """

  import Ecto.Query, warn: false
  alias FoodieFriends.Repo

  alias FoodieFriends.Messages.Message

  @doc """
  Returns the list of messages.

  ## Examples

      iex> list_messages()
      [%Message{}, ...]

  """
  def list_messages do
    Repo.all(Message)
  end

  # converts from struct to map to return to the client-side
  def list_messages_by_group_id(group_id) do
    query = from q in Message, where: q.group_id == ^group_id
    Repo.all(query)
      |> Repo.preload(:group)
      |> Repo.preload(:user)
      |> Enum.map(
        &%{
          msg_id: &1.id,
          group_id: &1.group_id,
          group_name: &1.group.name,
          group_desc: &1.group.desc,
          user_id: &1.user_id,
          user_email: &1.user.email,
          user_fname: &1.user.fname,
          user_lname: &1.user.lname,
          msg: &1.msg,
          timestamp: &1.inserted_at
        })
  end

  @doc """
  Gets a single message.

  Raises `Ecto.NoResultsError` if the Message does not exist.

  ## Examples

      iex> get_message!(123)
      %Message{}

      iex> get_message!(456)
      ** (Ecto.NoResultsError)

  """
  def get_message!(id), do: Repo.get!(Message, id)

  @doc """
  Creates a message.

  ## Examples

      iex> create_message(%{field: value})
      {:ok, %Message{}}

      iex> create_message(%{field: bad_value})
      {:error, %Ecto.Changeset{}}

  """
  def create_message(attrs \\ %{}) do
    %Message{}
    |> Message.changeset(attrs)
    |> Repo.insert()
  end

  @doc """
  Updates a message.

  ## Examples

      iex> update_message(message, %{field: new_value})
      {:ok, %Message{}}

      iex> update_message(message, %{field: bad_value})
      {:error, %Ecto.Changeset{}}

  """
  def update_message(%Message{} = message, attrs) do
    message
    |> Message.changeset(attrs)
    |> Repo.update()
  end

  @doc """
  Deletes a Message.

  ## Examples

      iex> delete_message(message)
      {:ok, %Message{}}

      iex> delete_message(message)
      {:error, %Ecto.Changeset{}}

  """
  def delete_message(%Message{} = message) do
    Repo.delete(message)
  end

  @doc """
  Returns an `%Ecto.Changeset{}` for tracking message changes.

  ## Examples

      iex> change_message(message)
      %Ecto.Changeset{source: %Message{}}

  """
  def change_message(%Message{} = message) do
    Message.changeset(message, %{})
  end
end
