use Mix.Config

# We don't run a server during test. If one is required,
# you can enable the server option below.
config :foodiefriends, FoodieFriendsWeb.Endpoint,
  http: [port: 4002],
  server: false

# Print only warnings and errors during test
config :logger, level: :warn

# Configure your database
config :foodiefriends, FoodieFriends.Repo,
  username: "INSERT_HERE",
  password: "INSERT_HERE",
  database: "INSERT_HERE",
  hostname: "localhost",
  pool: Ecto.Adapters.SQL.Sandbox
