defmodule MemoryWeb.GamesChannel do
  use MemoryWeb, :channel

  alias Memory.Game
  alias Memory.BackupAgent

  def join("games:" <> name, payload, socket) do
    if authorized?(payload) do
      #check first if name is already stored, else create new game
      game = Memory.BackupAgent.get(name) || Game.initializeNewGame()
      socket = socket
        |> assign(:game, game)
        |> assign(:name, name)
      #store the name of the game
      Memory.BackupAgent.put(name, game)
      {:ok, %{"join" => name, "game" => Game.getClientViewModel(game)}, socket}
    else
      {:error, %{reason: "unauthorized"}}
    end
  end

  def handle_in("revealTile", %{"firstIndex" => firstIndex }, socket) do
    name = socket.assigns[:name]
    game = Game.incrementClickCountInGame(socket.assigns[:game])
    socket = assign(socket, :game, game)
    #need to "restore" the state of the game after each change
    Memory.BackupAgent.put(name, game)
    {:reply, {:ok, %{ "game" => Game.revealSingleTile(game, firstIndex)}}, socket}
  end

  def handle_in("matchTiles", %{"firstIndex" => firstIndex, "secondIndex" => secondIndex }, socket) do
    name = socket.assigns[:name]
    game = Game.matchTiles(socket.assigns[:game], firstIndex, secondIndex)
    socket = assign(socket, :game, game)
    #need to "restore" the state of the game after each change
    Memory.BackupAgent.put(name, game)
    {:reply, {:ok, %{ "game" => Game.revealBothTiles(game, firstIndex, secondIndex)}}, socket}
  end

  def handle_in("getUpdate", payload, socket) do
    game = socket.assigns[:game]
    {:reply, {:ok, %{ "game" => Game.getClientViewModel(game)}}, socket}
  end

  def handle_in("resetGame", payload, socket) do
    name = socket.assigns[:name]
    game = Game.initializeNewGame()
    socket = assign(socket, :game, game)
    #need to "restore" the state of the game after each change
    Memory.BackupAgent.put(name, game)
    {:reply, {:ok, %{ "game" => Game.getClientViewModel(game)}}, socket}
  end

  defp authorized?(_payload) do
    true
  end
end