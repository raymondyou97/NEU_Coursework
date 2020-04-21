# This file is responsible for configuring your application
# and its dependencies with the aid of the Mix.Config module.
#
# This configuration file is loaded before any dependency and
# is restricted to this project.

# General application configuration
use Mix.Config

config :foodiefriends,
  ecto_repos: [FoodieFriends.Repo]

# Configures the endpoint
config :foodiefriends, FoodieFriendsWeb.Endpoint,
  url: [host: "localhost"],
  secret_key_base: "9ikEMeYtETJG0ttcoLwSBjryWp3ZE4M6crRllDPtzhHRLMET/iJCOQO/0Lbb6TBi",
  render_errors: [view: FoodieFriendsWeb.ErrorView, accepts: ~w(html json)],
  pubsub: [name: FoodieFriends.PubSub, adapter: Phoenix.PubSub.PG2]

# Configures Elixir's Logger
config :logger, :console,
  format: "$time $metadata[$level] $message\n",
  metadata: [:request_id]

# Use Jason for JSON parsing in Phoenix
config :phoenix, :json_library, Jason

# Import environment specific config. This must remain at the bottom
# of this file so it overrides the configuration defined above.
import_config "#{Mix.env()}.exs"

config :ex_aws,
  access_key_id: "INSERT_HERE",
  secret_access_key: "INSERT_HERE",
  bucket: "INSERT_HERE",
  region: "INSERT_HERE"