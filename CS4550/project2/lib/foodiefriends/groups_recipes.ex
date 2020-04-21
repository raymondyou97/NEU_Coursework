defmodule FoodieFriends.GroupsRecipes do
  @moduledoc """
  The GroupsRecipes context.
  """

  import Ecto.Query, warn: false
  alias FoodieFriends.Repo

  alias FoodieFriends.GroupsRecipes.GroupsRecipe

  @doc """
  Returns the list of groupsrecipes.

  ## Examples

      iex> list_groupsrecipes()
      [%GroupsRecipe{}, ...]

  """
  def list_groupsrecipes do
    Repo.all(GroupsRecipe)
    |> Repo.preload(:group)
    |> Repo.preload(:recipe)

  end

  @doc """
  Gets a single groups_recipe.

  Raises `Ecto.NoResultsError` if the Groups recipe does not exist.

  ## Examples

      iex> get_groups_recipe!(123)
      %GroupsRecipe{}

      iex> get_groups_recipe!(456)
      ** (Ecto.NoResultsError)

  """
  def get_groups_recipe!(id), do: Repo.get!(GroupsRecipe, id)

  @doc """
  Creates a groups_recipe.

  ## Examples

      iex> create_groups_recipe(%{field: value})
      {:ok, %GroupsRecipe{}}

      iex> create_groups_recipe(%{field: bad_value})
      {:error, %Ecto.Changeset{}}

  """
  def create_groups_recipe(attrs \\ %{}) do
    %GroupsRecipe{}
    |> GroupsRecipe.changeset(attrs)
    |> Repo.insert()
  end

  @doc """
  Updates a groups_recipe.

  ## Examples

      iex> update_groups_recipe(groups_recipe, %{field: new_value})
      {:ok, %GroupsRecipe{}}

      iex> update_groups_recipe(groups_recipe, %{field: bad_value})
      {:error, %Ecto.Changeset{}}

  """
  def update_groups_recipe(%GroupsRecipe{} = groups_recipe, attrs) do
    groups_recipe
    |> GroupsRecipe.changeset(attrs)
    |> Repo.update()
  end

  @doc """
  Deletes a GroupsRecipe.

  ## Examples

      iex> delete_groups_recipe(groups_recipe)
      {:ok, %GroupsRecipe{}}

      iex> delete_groups_recipe(groups_recipe)
      {:error, %Ecto.Changeset{}}

  """
  def delete_groups_recipe(%GroupsRecipe{} = groups_recipe) do
    Repo.delete(groups_recipe)
  end

  @doc """
  Returns an `%Ecto.Changeset{}` for tracking groups_recipes changes.

  ## Examples

      iex> change_groups_recipe(groups_recipe)
      %Ecto.Changeset{source: %GroupsRecipe{}}

  """
  def change_groups_recipe(%GroupsRecipe{} = groups_recipe) do
    GroupsRecipe.changeset(groups_recipe, %{})
  end
end
