defmodule FoodieFriends.GroupsRecipesTest do
  use FoodieFriends.DataCase

  alias FoodieFriends.GroupsRecipes

  describe "groupsrecipes" do
    alias FoodieFriends.GroupsRecipes.GroupsRecipe

    @valid_attrs %{group: 42, recipe: 42}
    @update_attrs %{group: 43, recipe: 43}
    @invalid_attrs %{group: nil, recipe: nil}

    def groupsrecipes_fixture(attrs \\ %{}) do
      {:ok, groupsrecipes} =
        attrs
        |> Enum.into(@valid_attrs)
        |> GroupsRecipes.create_groupsrecipes()

      groupsrecipes
    end

    test "list_groupsrecipes/0 returns all groupsrecipes" do
      groupsrecipes = groupsrecipes_fixture()
      assert GroupsRecipes.list_groupsrecipes() == [groupsrecipes]
    end

    test "get_groupsrecipes!/1 returns the groupsrecipes with given id" do
      groupsrecipes = groupsrecipes_fixture()
      assert GroupsRecipes.get_groupsrecipes!(groupsrecipes.id) == groupsrecipes
    end

    test "create_groupsrecipes/1 with valid data creates a groupsrecipes" do
      assert {:ok, %GroupsRecipe{} = groupsrecipes} = GroupsRecipes.create_groupsrecipes(@valid_attrs)
      assert groupsrecipes.group == 42
      assert groupsrecipes.recipe == 42
    end

    test "create_groupsrecipes/1 with invalid data returns error changeset" do
      assert {:error, %Ecto.Changeset{}} = GroupsRecipes.create_groupsrecipes(@invalid_attrs)
    end

    test "update_groupsrecipes/2 with valid data updates the groupsrecipes" do
      groupsrecipes = groupsrecipes_fixture()
      assert {:ok, %GroupsRecipe{} = groupsrecipes} = GroupsRecipes.update_groupsrecipes(groupsrecipes, @update_attrs)
      assert groupsrecipes.group == 43
      assert groupsrecipes.recipe == 43
    end

    test "update_groupsrecipes/2 with invalid data returns error changeset" do
      groupsrecipes = groupsrecipes_fixture()
      assert {:error, %Ecto.Changeset{}} = GroupsRecipes.update_groupsrecipes(groupsrecipes, @invalid_attrs)
      assert groupsrecipes == GroupsRecipes.get_groupsrecipes!(groupsrecipes.id)
    end

    test "delete_groupsrecipes/1 deletes the groupsrecipes" do
      groupsrecipes = groupsrecipes_fixture()
      assert {:ok, %GroupsRecipe{}} = GroupsRecipes.delete_groupsrecipes(groupsrecipes)
      assert_raise Ecto.NoResultsError, fn -> GroupsRecipes.get_groupsrecipes!(groupsrecipes.id) end
    end

    test "change_groupsrecipes/1 returns a groupsrecipes changeset" do
      groupsrecipes = groupsrecipes_fixture()
      assert %Ecto.Changeset{} = GroupsRecipes.change_groupsrecipes(groupsrecipes)
    end
  end
end
