defmodule FoodieFriends.UsersGroups do
  @moduledoc """
  The UsersGroups context.
  """

  import Ecto.Query, warn: false
  alias FoodieFriends.Repo

  alias FoodieFriends.UsersGroups.UsersGroup

  @doc """
  Returns the list of usersgroups.

  ## Examples

      iex> list_usersgroups()
      [%UsersGroup{}, ...]

  """
  def list_usersgroups do
    Repo.all(UsersGroup)
      |> Repo.preload(:user)
      |> Repo.preload(:group)
  end

  @doc """
  Gets a single users_group.

  Raises `Ecto.NoResultsError` if the Users group does not exist.

  ## Examples

      iex> get_users_group!(123)
      %UsersGroup{}

      iex> get_users_group!(456)
      ** (Ecto.NoResultsError)

  """
  def get_users_group!(id), do: Repo.get!(UsersGroup, id)

  @doc """
  Creates a users_group.

  ## Examples

      iex> create_users_group(%{field: value})
      {:ok, %UsersGroup{}}

      iex> create_users_group(%{field: bad_value})
      {:error, %Ecto.Changeset{}}

  """
  def create_users_group(attrs \\ %{}) do
    %UsersGroup{}
    |> UsersGroup.changeset(attrs)
    |> Repo.insert()
  end

  @doc """
  Updates a users_group.

  ## Examples

      iex> update_users_group(users_group, %{field: new_value})
      {:ok, %UsersGroup{}}

      iex> update_users_group(users_group, %{field: bad_value})
      {:error, %Ecto.Changeset{}}

  """
  def update_users_group(%UsersGroup{} = users_group, attrs) do
    users_group
    |> UsersGroup.changeset(attrs)
    |> Repo.update()
  end

  @doc """
  Deletes a UsersGroup.

  ## Examples

      iex> delete_users_group(users_group)
      {:ok, %UsersGroup{}}

      iex> delete_users_group(users_group)
      {:error, %Ecto.Changeset{}}

  """
  def delete_users_group(%UsersGroup{} = users_group) do
    Repo.delete(users_group)
  end

  @doc """
  Returns an `%Ecto.Changeset{}` for tracking users_group changes.

  ## Examples

      iex> change_users_group(users_group)
      %Ecto.Changeset{source: %UsersGroup{}}

  """
  def change_users_group(%UsersGroup{} = users_group) do
    UsersGroup.changeset(users_group, %{})
  end
end
