defmodule FoodieFriendsWeb.GroupsRecipeControllerTest do
  use FoodieFriendsWeb.ConnCase

  alias FoodieFriends.GroupsRecipes
  alias FoodieFriends.GroupsRecipes.GroupsRecipe

  @create_attrs %{
    group: 42,
    recipe: 42
  }
  @update_attrs %{
    group: 43,
    recipe: 43
  }
  @invalid_attrs %{group: nil, recipe: nil}

  def fixture(:groupsrecipes) do
    {:ok, groupsrecipes} = GroupsRecipes.create_groupsrecipes(@create_attrs)
    groupsrecipes
  end

  setup %{conn: conn} do
    {:ok, conn: put_req_header(conn, "accept", "application/json")}
  end

  describe "index" do
    test "lists all groupsrecipes", %{conn: conn} do
      conn = get(conn, Routes.groupsrecipes_path(conn, :index))
      assert json_response(conn, 200)["data"] == []
    end
  end

  describe "create groupsrecipes" do
    test "renders groupsrecipes when data is valid", %{conn: conn} do
      conn = post(conn, Routes.groupsrecipes_path(conn, :create), groupsrecipes: @create_attrs)
      assert %{"id" => id} = json_response(conn, 201)["data"]

      conn = get(conn, Routes.groupsrecipes_path(conn, :show, id))

      assert %{
               "id" => id,
               "group" => 42,
               "recipe" => 42
             } = json_response(conn, 200)["data"]
    end

    test "renders errors when data is invalid", %{conn: conn} do
      conn = post(conn, Routes.groupsrecipes_path(conn, :create), groupsrecipes: @invalid_attrs)
      assert json_response(conn, 422)["errors"] != %{}
    end
  end

  describe "update groupsrecipes" do
    setup [:create_groupsrecipes]

    test "renders groupsrecipes when data is valid", %{conn: conn, groupsrecipes: %GroupsRecipe{id: id} = groupsrecipes} do
      conn = put(conn, Routes.groupsrecipes_path(conn, :update, groupsrecipes), groupsrecipes: @update_attrs)
      assert %{"id" => ^id} = json_response(conn, 200)["data"]

      conn = get(conn, Routes.groupsrecipes_path(conn, :show, id))

      assert %{
               "id" => id,
               "group" => 43,
               "recipe" => 43
             } = json_response(conn, 200)["data"]
    end

    test "renders errors when data is invalid", %{conn: conn, groupsrecipes: groupsrecipes} do
      conn = put(conn, Routes.groupsrecipes_path(conn, :update, groupsrecipes), groupsrecipes: @invalid_attrs)
      assert json_response(conn, 422)["errors"] != %{}
    end
  end

  describe "delete groupsrecipes" do
    setup [:create_groupsrecipes]

    test "deletes chosen groupsrecipes", %{conn: conn, groupsrecipes: groupsrecipes} do
      conn = delete(conn, Routes.groupsrecipes_path(conn, :delete, groupsrecipes))
      assert response(conn, 204)

      assert_error_sent 404, fn ->
        get(conn, Routes.groupsrecipes_path(conn, :show, groupsrecipes))
      end
    end
  end

  defp create_groupsrecipes(_) do
    groupsrecipes = fixture(:groupsrecipes)
    {:ok, groupsrecipes: groupsrecipes}
  end
end
