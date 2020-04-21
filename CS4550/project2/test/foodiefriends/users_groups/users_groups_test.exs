defmodule FoodieFriends.UsersGroupsTest do
  use FoodieFriends.DataCase

  alias FoodieFriends.UsersGroups

  describe "usersgroups" do
    alias FoodieFriends.UsersGroups.UsersGroup

    @valid_attrs %{}
    @update_attrs %{}
    @invalid_attrs %{}

    def users_group_fixture(attrs \\ %{}) do
      {:ok, users_group} =
        attrs
        |> Enum.into(@valid_attrs)
        |> UsersGroups.create_users_group()

      users_group
    end

    test "list_usersgroups/0 returns all usersgroups" do
      users_group = users_group_fixture()
      assert UsersGroups.list_usersgroups() == [users_group]
    end

    test "get_users_group!/1 returns the users_group with given id" do
      users_group = users_group_fixture()
      assert UsersGroups.get_users_group!(users_group.id) == users_group
    end

    test "create_users_group/1 with valid data creates a users_group" do
      assert {:ok, %UsersGroup{} = users_group} = UsersGroups.create_users_group(@valid_attrs)
    end

    test "create_users_group/1 with invalid data returns error changeset" do
      assert {:error, %Ecto.Changeset{}} = UsersGroups.create_users_group(@invalid_attrs)
    end

    test "update_users_group/2 with valid data updates the users_group" do
      users_group = users_group_fixture()
      assert {:ok, %UsersGroup{} = users_group} = UsersGroups.update_users_group(users_group, @update_attrs)
    end

    test "update_users_group/2 with invalid data returns error changeset" do
      users_group = users_group_fixture()
      assert {:error, %Ecto.Changeset{}} = UsersGroups.update_users_group(users_group, @invalid_attrs)
      assert users_group == UsersGroups.get_users_group!(users_group.id)
    end

    test "delete_users_group/1 deletes the users_group" do
      users_group = users_group_fixture()
      assert {:ok, %UsersGroup{}} = UsersGroups.delete_users_group(users_group)
      assert_raise Ecto.NoResultsError, fn -> UsersGroups.get_users_group!(users_group.id) end
    end

    test "change_users_group/1 returns a users_group changeset" do
      users_group = users_group_fixture()
      assert %Ecto.Changeset{} = UsersGroups.change_users_group(users_group)
    end
  end
end
