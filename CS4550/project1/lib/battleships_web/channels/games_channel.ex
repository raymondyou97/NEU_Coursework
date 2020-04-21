defmodule BattleshipsWeb.GamesChannel do
  use BattleshipsWeb, :channel

  alias Battleships.Game
  alias Battleships.GameServer

  def join("games:" <> gameName, payload, socket) do
    if authorized?(payload) do
      playerName = Map.get(payload, "playerName")
      GameServer.start(gameName)
      game = GameServer.peek(gameName)
      cond do
        #load up the player view if it already exists
        Game.checkIfPlayerExists(game, playerName) ->
          game = GameServer.peek(gameName)
          socket = socket
          |> assign(:gameName, gameName)
          |> assign(:playerName, playerName)
          |> assign(:game, game)
          newClientView = Game.clientViewBeforeAttackPhase(game)
          viewModel = %{"gameName" => gameName, "game" => newClientView, "currentPlayerName" => playerName}
          {:ok, viewModel, socket}
        #unable to join if already 2 players
        Game.checkIfTwoPlayersExist(game) ->
          {:error, %{reason: "The game with the name '#{gameName}' already has two players!"}}
        #add new player
        true ->
          GameServer.addPlayer(gameName, playerName)
          game = GameServer.peek(gameName)
          socket = socket
          |> assign(:gameName, gameName)
          |> assign(:playerName, playerName)
          |> assign(:game, game)
          newClientView = Game.clientViewBeforeAttackPhase(game)
          viewModel = %{"gameName" => gameName, "game" => newClientView, "currentPlayerName" => playerName}
          send(self(), {:newPlayer, viewModel})
          {:ok, viewModel, socket}
      end
    else
      {:error, %{reason: "unauthorized"}}
    end
  end

  def handle_info({:newPlayer, viewModel}, socket) do
    broadcast!(socket, "newPlayerHasJoined", viewModel)
    {:noreply, socket}
  end

  def handle_in("addShip", %{"playerName" => playerName, "index" => index, "length" => length, "orientation" => orientation}, socket) do
      gameName = socket.assigns[:gameName]
      game = GameServer.peek(gameName)
      cond do
        (Game.outOfBound?(index, length, orientation)) ->
          {:reply, {:error, %{reason: "ERROR: Ship placed out of bounds!"}}, socket}
        (Game.shipCollision?(game, index, length, orientation, playerName)) ->
          {:reply, {:error, %{reason: "ERROR: Ship collision!"}}, socket}
        true ->
          GameServer.addShip(gameName, index, length, orientation, playerName)
          game = GameServer.peek(gameName)
          socket = socket
          |> assign(:gameName, gameName)
          |> assign(:playerName, playerName)
          |> assign(:game, game)
          newClientView = Game.clientViewBeforeAttackPhase(game)
          viewModel = %{"gameName" => gameName, "game" => newClientView, "currentPlayerName" => playerName}
          broadcast!(socket, "addShip", viewModel)
          {:reply, {:ok, viewModel}, socket}
      end
  end

  def handle_in("playerReady", %{"playerName" => playerName}, socket) do
    gameName = socket.assigns[:gameName]
    GameServer.playerReady(gameName, playerName)
    game = GameServer.peek(gameName)
    socket = socket
      |> assign(:gameName, gameName)
      |> assign(:playerName, playerName)
      |> assign(:game, game)
    newClientView = Game.clientViewBeforeAttackPhase(game)
    viewModel = %{"gameName" => gameName, "game" => newClientView, "currentPlayerName" => playerName}
    broadcast!(socket, "playerIsReady", viewModel)
    {:reply, {:ok, viewModel}, socket}
  end

  def handle_in("globalMessage", %{"message" => message}, socket) do
    gameName = socket.assigns[:gameName]
    playerName = socket.assigns[:playerName]
    GameServer.globalMessage(gameName, message)
    game = GameServer.peek(gameName)
    socket = socket
      |> assign(:gameName, gameName)
      |> assign(:game, game)
    newClientView = Game.clientViewBeforeAttackPhase(game)
    viewModel = %{"gameName" => gameName, "game" => newClientView, "currentPlayerName" => playerName}
    broadcast!(socket, "incomingGlobalMessage", viewModel)
    {:reply, {:ok, viewModel}, socket}
  end

  def handle_in("beginAttackPhase", %{"playerName" => playerName}, socket) do
    gameName = socket.assigns[:gameName]
    GameServer.beginAttackPhase(gameName)
    game = GameServer.peek(gameName)
    socket = socket
      |> assign(:gameName, gameName)
      |> assign(:playerName, playerName)
      |> assign(:game, game)
    newClientView = Game.clientViewInitialAttackPhase(game, playerName)
    viewModel = %{"gameName" => gameName, "game" => newClientView, "currentPlayerName" => playerName}
    broadcast!(socket, "attackPhaseStarted", viewModel)
    {:reply, {:ok, viewModel}, socket}
  end

  def handle_in("attack", %{"playerName" => playerName, "index" => index}, socket) do
    gameName = socket.assigns[:gameName]
    GameServer.attack(gameName, playerName, index)
    game = GameServer.peek(gameName)
    socket = socket
    |> assign(:gameName, gameName)
    |> assign(:playerName, playerName)
    |> assign(:game, game)
    player1View = Game.clientViewOfShotsForPlayerOne(game, playerName)
    player2View = Game.clientViewOfShotsForPlayerTwo(game, playerName)
    viewModel = %{"gameName" => gameName, "player1View" => player1View, "player2View" => player2View, "currentPlayerName" => playerName}
    broadcast!(socket, "attackIncoming", viewModel)
    {:reply, {:ok, viewModel}, socket}
  end

  def handle_in("reset", nil, socket) do
    gameName = socket.assigns[:gameName]
    playerName = socket.assigns[:playerName]
    GameServer.reset(gameName)
    game = GameServer.peek(gameName)

    socket = socket
    |> assign(:gameName, gameName)
    |> assign(:game, game)

    newClientView = Game.clientViewBeforeAttackPhase(game)
    viewModel = %{"gameName" => gameName, "game" => newClientView, "playerName" => playerName}
    broadcast!(socket, "reset", viewModel)
    {:reply, {:ok, viewModel}, socket}
  end

  def handle_in("chatMessage", %{"playerName" => playerName, "message" => message}, socket) do
    gameName = socket.assigns[:gameName]
    GameServer.chatMessage(gameName, playerName, message)
    game = GameServer.peek(gameName)
    socket = socket
    |> assign(:gameName, gameName)
    |> assign(:playerName, playerName)
    |> assign(:game, game)

    newClientView = Game.clientViewOfChatRoom(game)
    viewModel = %{"game" => newClientView}
    broadcast!(socket, "newChatMessage", viewModel)
    {:noreply, socket}
  end

  # Add authorization logic here as required.
  defp authorized?(_payload) do
    true
  end
end
