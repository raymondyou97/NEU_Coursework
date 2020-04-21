defmodule FoodieFriendsWeb.ImageController do
    use FoodieFriendsWeb, :controller
    
    def create(conn, %{"image" => base64_encoding}) do
      aws_s3_img_url = FoodieFriends.ImageUploader.upload_image(base64_encoding)
      conn
        |> put_status(:created)
        |> json(%{"image_url" => aws_s3_img_url})
    end
  end