# Most of the code here taken from https://dockyard.com/blog/2017/08/22/building-an-image-upload-api-with-phoenix
# Some taken from https://stackoverflow.com/questions/39031161/how-do-you-handle-base64-encoded-files-in-elixir
defmodule FoodieFriends.ImageUploader do
  alias ExAws.S3
  
  def upload_image(input) do
    # get the bucket and region name
    bucket_name = Application.get_env(:ex_aws, :bucket)
    region_name = Application.get_env(:ex_aws, :region)
  
    # Decode the base 64 string
    {start, length} = :binary.match(input, ";base64,")
    raw = :binary.part(input, start + length, byte_size(input) - start - length)
    {:ok, image_binary} = Base.decode64(raw)

    # Generate a unique filename
    filename = image_binary
      |> image_extension()
      |> unique_filename()

    # Upload to S3
    _response = S3.put_object(bucket_name, filename, image_binary) 
      |> ExAws.request!

    # Generate and returnthe full URL to the newly uploaded image
    "https://s3.#{region_name}.amazonaws.com/#{bucket_name}/#{filename}"
  end
  
  # Generates a unique filename with a given extension
  defp unique_filename(extension) do
    UUID.uuid4(:hex) <> extension
  end
  
  # Helper functions to read the binary to determine the image extension
  defp image_extension(<<0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, _::binary>>), do: ".png"
  
  defp image_extension(<<0xff, 0xD8, _::binary>>), do: ".jpg"
end