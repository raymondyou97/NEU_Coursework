defmodule Battleships.Application do
  # See https://hexdocs.pm/elixir/Application.html
  # for more information on OTP Applications
  @moduledoc false

  use Application

  def start(_type, _args) do
    # List all child processes to be supervised
    children = [
      # Start the endpoint when the application starts
      BattleshipsWeb.Endpoint,
      # Starts a worker by calling: Battleships.Worker.start_link(arg)
      # {Battleships.Worker, arg},
      Battleships.GameSup,
      Battleships.BackupAgent,
    ]

    # See https://hexdocs.pm/elixir/Supervisor.html
    # for other strategies and supported options
    opts = [strategy: :one_for_one, name: Battleships.Supervisor]
    Supervisor.start_link(children, opts)
  end

  # Tell Phoenix to update the endpoint configuration
  # whenever the application is updated.
  def config_change(changed, _new, removed) do
    BattleshipsWeb.Endpoint.config_change(changed, removed)
    :ok
  end
end
