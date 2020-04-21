defmodule FoodieFriends.RecipesTest do
  use FoodieFriends.DataCase

  alias FoodieFriends.Recipes

  describe "recipes" do
    alias FoodieFriends.Recipes.Recipe

    @valid_attrs %{cooktime: 42, courses: "some courses", image_url: "some image_url", ingredients: "some ingredients", name: "some name", rating: 42, recipe_id: "some recipe_id"}
    @update_attrs %{cooktime: 43, courses: "some updated courses", image_url: "some updated image_url", ingredients: "some updated ingredients", name: "some updated name", rating: 43, recipe_id: "some updated recipe_id"}
    @invalid_attrs %{cooktime: nil, courses: nil, image_url: nil, ingredients: nil, name: nil, rating: nil, recipe_id: nil}

    def recipe_fixture(attrs \\ %{}) do
      {:ok, recipe} =
        attrs
        |> Enum.into(@valid_attrs)
        |> Recipes.create_recipe()

      recipe
    end

    test "list_recipes/0 returns all recipes" do
      recipe = recipe_fixture()
      assert Recipes.list_recipes() == [recipe]
    end

    test "get_recipe!/1 returns the recipe with given id" do
      recipe = recipe_fixture()
      assert Recipes.get_recipe!(recipe.id) == recipe
    end

    test "create_recipe/1 with valid data creates a recipe" do
      assert {:ok, %Recipe{} = recipe} = Recipes.create_recipe(@valid_attrs)
      assert recipe.cooktime == 42
      assert recipe.courses == "some courses"
      assert recipe.image_url == "some image_url"
      assert recipe.ingredients == "some ingredients"
      assert recipe.name == "some name"
      assert recipe.rating == 42
      assert recipe.recipe_id == "some recipe_id"
    end

    test "create_recipe/1 with invalid data returns error changeset" do
      assert {:error, %Ecto.Changeset{}} = Recipes.create_recipe(@invalid_attrs)
    end

    test "update_recipe/2 with valid data updates the recipe" do
      recipe = recipe_fixture()
      assert {:ok, %Recipe{} = recipe} = Recipes.update_recipe(recipe, @update_attrs)
      assert recipe.cooktime == 43
      assert recipe.courses == "some updated courses"
      assert recipe.image_url == "some updated image_url"
      assert recipe.ingredients == "some updated ingredients"
      assert recipe.name == "some updated name"
      assert recipe.rating == 43
      assert recipe.recipe_id == "some updated recipe_id"
    end

    test "update_recipe/2 with invalid data returns error changeset" do
      recipe = recipe_fixture()
      assert {:error, %Ecto.Changeset{}} = Recipes.update_recipe(recipe, @invalid_attrs)
      assert recipe == Recipes.get_recipe!(recipe.id)
    end

    test "delete_recipe/1 deletes the recipe" do
      recipe = recipe_fixture()
      assert {:ok, %Recipe{}} = Recipes.delete_recipe(recipe)
      assert_raise Ecto.NoResultsError, fn -> Recipes.get_recipe!(recipe.id) end
    end

    test "change_recipe/1 returns a recipe changeset" do
      recipe = recipe_fixture()
      assert %Ecto.Changeset{} = Recipes.change_recipe(recipe)
    end
  end
end
