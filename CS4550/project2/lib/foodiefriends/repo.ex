defmodule FoodieFriends.Repo do
  use Ecto.Repo,
    otp_app: :foodiefriends,
    adapter: Ecto.Adapters.Postgres
end
