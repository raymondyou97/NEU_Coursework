defmodule FoodieFriendsWeb.SearchRecipeController do
    use FoodieFriendsWeb, :controller
  
    # alias FoodieFriends.Users
    # alias FoodieFriends.Users.User
  
    action_fallback FoodieFriendsWeb.FallbackController
  
    def create(conn, %{"search_params" => search_params}) do
        app_id = Application.get_env(:foodiefriends, :yummly_api_keys)[:applicationId]
        app_key = Application.get_env(:foodiefriends, :yummly_api_keys)[:applicationKey]
        apiUrl = "http://api.yummly.com/v1/api/recipes?_app_id=#{app_id}&_app_key=#{app_key}&q="
            <> search_params <> "&maxResult=60"

        case HTTPoison.get(apiUrl) do
            {:ok, %HTTPoison.Response{body: body, status_code: 200}} ->
              results = Jason.decode!(body)
              conn
                |> put_resp_header("content-type", "application/json; charset=utf-8")
                |> send_resp(:created, Jason.encode!(%{data: results}))
            {:ok, %HTTPoison.Response{status_code: 404}} ->
              IO.puts "Not found"
            {:error, %HTTPoison.Error{reason: reason}} ->
              IO.inspect reason
        end
    end

    def show(conn, %{"id" => recipe_id}) do
      app_id = Application.get_env(:foodiefriends, :yummly_api_keys)[:applicationId]
      app_key = Application.get_env(:foodiefriends, :yummly_api_keys)[:applicationKey]
      apiUrl = "http://api.yummly.com/v1/api/recipe/#{recipe_id}?_app_id=#{app_id}&_app_key=#{app_key}"

      case HTTPoison.get(apiUrl) do
        {:ok, %HTTPoison.Response{body: body, status_code: 200}} ->
          results = Jason.decode!(body)
          conn
            |> put_resp_header("content-type", "application/json; charset=utf-8")
            |> send_resp(:created, Jason.encode!(%{data: results}))
        {:ok, %HTTPoison.Response{status_code: 404}} ->
          IO.puts "Not found"
        {:error, %HTTPoison.Error{reason: reason}} ->
          IO.inspect reason
      end
    end
  end
  