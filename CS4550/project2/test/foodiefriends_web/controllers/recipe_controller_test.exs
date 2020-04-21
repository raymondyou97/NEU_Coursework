defmodule FoodieFriendsWeb.RecipeControllerTest do
  use FoodieFriendsWeb.ConnCase

  alias FoodieFriends.Recipes
  alias FoodieFriends.Recipes.Recipe

  @create_attrs %{
    cooktime: 42,
    courses: "some courses",
    image_url: "some image_url",
    ingredients: "some ingredients",
    name: "some name",
    rating: 42,
    recipe_id: "some recipe_id"
  }
  @update_attrs %{
    cooktime: 43,
    courses: "some updated courses",
    image_url: "some updated image_url",
    ingredients: "some updated ingredients",
    name: "some updated name",
    rating: 43,
    recipe_id: "some updated recipe_id"
  }
  @invalid_attrs %{cooktime: nil, courses: nil, image_url: nil, ingredients: nil, name: nil, rating: nil, recipe_id: nil}

  def fixture(:recipe) do
    {:ok, recipe} = Recipes.create_recipe(@create_attrs)
    recipe
  end

  setup %{conn: conn} do
    {:ok, conn: put_req_header(conn, "accept", "application/json")}
  end

  describe "index" do
    test "lists all recipes", %{conn: conn} do
      conn = get(conn, Routes.recipe_path(conn, :index))
      assert json_response(conn, 200)["data"] == []
    end
  end

  describe "create recipe" do
    test "renders recipe when data is valid", %{conn: conn} do
      conn = post(conn, Routes.recipe_path(conn, :create), recipe: @create_attrs)
      assert %{"id" => id} = json_response(conn, 201)["data"]

      conn = get(conn, Routes.recipe_path(conn, :show, id))

      assert %{
               "id" => id,
               "cooktime" => 42,
               "courses" => "some courses",
               "image_url" => "some image_url",
               "ingredients" => "some ingredients",
               "name" => "some name",
               "rating" => 42,
               "recipe_id" => "some recipe_id"
             } = json_response(conn, 200)["data"]
    end

    test "renders errors when data is invalid", %{conn: conn} do
      conn = post(conn, Routes.recipe_path(conn, :create), recipe: @invalid_attrs)
      assert json_response(conn, 422)["errors"] != %{}
    end
  end

  describe "update recipe" do
    setup [:create_recipe]

    test "renders recipe when data is valid", %{conn: conn, recipe: %Recipe{id: id} = recipe} do
      conn = put(conn, Routes.recipe_path(conn, :update, recipe), recipe: @update_attrs)
      assert %{"id" => ^id} = json_response(conn, 200)["data"]

      conn = get(conn, Routes.recipe_path(conn, :show, id))

      assert %{
               "id" => id,
               "cooktime" => 43,
               "courses" => "some updated courses",
               "image_url" => "some updated image_url",
               "ingredients" => "some updated ingredients",
               "name" => "some updated name",
               "rating" => 43,
               "recipe_id" => "some updated recipe_id"
             } = json_response(conn, 200)["data"]
    end

    test "renders errors when data is invalid", %{conn: conn, recipe: recipe} do
      conn = put(conn, Routes.recipe_path(conn, :update, recipe), recipe: @invalid_attrs)
      assert json_response(conn, 422)["errors"] != %{}
    end
  end

  describe "delete recipe" do
    setup [:create_recipe]

    test "deletes chosen recipe", %{conn: conn, recipe: recipe} do
      conn = delete(conn, Routes.recipe_path(conn, :delete, recipe))
      assert response(conn, 204)

      assert_error_sent 404, fn ->
        get(conn, Routes.recipe_path(conn, :show, recipe))
      end
    end
  end

  defp create_recipe(_) do
    recipe = fixture(:recipe)
    {:ok, recipe: recipe}
  end
end
