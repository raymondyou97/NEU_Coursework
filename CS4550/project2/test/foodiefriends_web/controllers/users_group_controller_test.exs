defmodule FoodieFriendsWeb.UsersGroupControllerTest do
  use FoodieFriendsWeb.ConnCase

  alias FoodieFriends.UsersGroups
  alias FoodieFriends.UsersGroups.UsersGroup

  @create_attrs %{

  }
  @update_attrs %{

  }
  @invalid_attrs %{}

  def fixture(:users_group) do
    {:ok, users_group} = UsersGroups.create_users_group(@create_attrs)
    users_group
  end

  setup %{conn: conn} do
    {:ok, conn: put_req_header(conn, "accept", "application/json")}
  end

  describe "index" do
    test "lists all usersgroups", %{conn: conn} do
      conn = get(conn, Routes.users_group_path(conn, :index))
      assert json_response(conn, 200)["data"] == []
    end
  end

  describe "create users_group" do
    test "renders users_group when data is valid", %{conn: conn} do
      conn = post(conn, Routes.users_group_path(conn, :create), users_group: @create_attrs)
      assert %{"id" => id} = json_response(conn, 201)["data"]

      conn = get(conn, Routes.users_group_path(conn, :show, id))

      assert %{
               "id" => id
             } = json_response(conn, 200)["data"]
    end

    test "renders errors when data is invalid", %{conn: conn} do
      conn = post(conn, Routes.users_group_path(conn, :create), users_group: @invalid_attrs)
      assert json_response(conn, 422)["errors"] != %{}
    end
  end

  describe "update users_group" do
    setup [:create_users_group]

    test "renders users_group when data is valid", %{conn: conn, users_group: %UsersGroup{id: id} = users_group} do
      conn = put(conn, Routes.users_group_path(conn, :update, users_group), users_group: @update_attrs)
      assert %{"id" => ^id} = json_response(conn, 200)["data"]

      conn = get(conn, Routes.users_group_path(conn, :show, id))

      assert %{
               "id" => id
             } = json_response(conn, 200)["data"]
    end

    test "renders errors when data is invalid", %{conn: conn, users_group: users_group} do
      conn = put(conn, Routes.users_group_path(conn, :update, users_group), users_group: @invalid_attrs)
      assert json_response(conn, 422)["errors"] != %{}
    end
  end

  describe "delete users_group" do
    setup [:create_users_group]

    test "deletes chosen users_group", %{conn: conn, users_group: users_group} do
      conn = delete(conn, Routes.users_group_path(conn, :delete, users_group))
      assert response(conn, 204)

      assert_error_sent 404, fn ->
        get(conn, Routes.users_group_path(conn, :show, users_group))
      end
    end
  end

  defp create_users_group(_) do
    users_group = fixture(:users_group)
    {:ok, users_group: users_group}
  end
end
