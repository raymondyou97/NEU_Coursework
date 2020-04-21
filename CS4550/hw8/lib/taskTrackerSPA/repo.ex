defmodule TaskTrackerSPA.Repo do
  use Ecto.Repo,
    otp_app: :taskTrackerSPA,
    adapter: Ecto.Adapters.Postgres
end
