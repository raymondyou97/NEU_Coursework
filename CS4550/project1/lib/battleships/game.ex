defmodule Battleships.Game do
  def new do
    newBoard = generateEmptyBoardOfTiles()
    %{
      playerOneBoardOfTiles: newBoard,
      playerTwoBoardOfTiles: newBoard,
      playerOneName: "",
      playerTwoName: "",
      playerOneIndicesOfShips: MapSet.new(),
      playerTwoIndicesOfShips: MapSet.new(),
      playerOneReady: false,
      playerTwoReady: false,
      attackPhase: false,
      globalMessage: "",
      playerOneIndicesOfShots: MapSet.new(),
      playerTwoIndicesOfShots: MapSet.new(),
      currentPlayersTurn: "",
      isGameOver: false,
      chatMessages: []
    }
  end

  def clientViewBeforeAttackPhase(game) do
    playerOneBoard = getPlayerOneBoard(game)
    playerTwoBoard = getPlayerTwoBoard(game)
    %{
      playerOneBoardOfTiles: playerOneBoard,
      playerTwoBoardOfTiles: playerTwoBoard,
      playerOneName: game.playerOneName,
      playerTwoName: game.playerTwoName,
      playerOneReady: game.playerOneReady,
      playerTwoReady: game.playerTwoReady,
      attackPhase: game.attackPhase,
      globalMessage: game.globalMessage,
      chatMessages: game.chatMessages
    }
  end

  def clientViewOfChatRoom(game) do
    %{
      chatMessages: game.chatMessages
    }
  end

  def clientViewInitialAttackPhase(game, playerName) do
    playerBegin = game.playerOneName
    if(game.playerOneName == playerName) do
      playerOneBoard = getPlayerOneBoard(game)
      playerTwoBoard = generateEmptyBoardOfTiles()
      %{
        playerOneBoardOfTiles: playerOneBoard,
        playerTwoBoardOfTiles: playerTwoBoard,
        playerOneName: game.playerOneName,
        playerTwoName: game.playerTwoName,
        playerOneReady: true,
        playerTwoReady: true,
        attackPhase: true,
        globalMessage: game.globalMessage,
        currentPlayersTurn: playerBegin,
        chatMessages: game.chatMessages
      }
    else
      playerOneBoard = generateEmptyBoardOfTiles()
      playerTwoBoard = getPlayerTwoBoard(game)
      %{
        playerOneBoardOfTiles: playerOneBoard,
        playerTwoBoardOfTiles: playerTwoBoard,
        playerOneName: game.playerOneName,
        playerTwoName: game.playerTwoName,
        playerOneReady: true,
        playerTwoReady: true,
        attackPhase: true,
        globalMessage: game.globalMessage,
        currentPlayersTurn: playerBegin,
        chatMessages: game.chatMessages
      }
    end
  end

  def clientViewOfShotsForPlayerOne(game, playerName) do
    player1Won = checkIfPlayerOneWon(game)
    player2Won = checkIfPlayerTwoWon(game)

    if(player1Won || player2Won) do
      if(player1Won) do
        playerOneBoard = getPlayerOneBoardWithShotsAndShips(game)
        playerTwoBoard = getPlayerTwoBoardWithShotsAndShips(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "#{game.playerTwoName} has won!",
          currentPlayersTurn: "",
          isGameOver: true,
          chatMessages: game.chatMessages
        }
      else
        playerOneBoard = getPlayerOneBoardWithShotsAndShips(game)
        playerTwoBoard = getPlayerTwoBoardWithShotsAndShips(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "#{game.playerOneName} has won!",
          currentPlayersTurn: "",
          isGameOver: true,
          chatMessages: game.chatMessages
        }
      end
    #no one has won yet
    else
      if(playerName == game.playerOneName) do
        nextPlayersTurn = game.playerTwoName
        playerOneBoard = getPlayerOneBoardWithShotsAndShips(game)
        playerTwoBoard = getPlayerTwoBoardWithShots(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "It is currently #{nextPlayersTurn}'s turn to attack",
          currentPlayersTurn: nextPlayersTurn,
          isGameOver: false,
          chatMessages: game.chatMessages
        }
      else
        nextPlayersTurn = game.playerOneName
        playerOneBoard = getPlayerOneBoardWithShotsAndShips(game)
        playerTwoBoard = getPlayerTwoBoardWithShots(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "It is currently #{nextPlayersTurn}'s turn to attack",
          currentPlayersTurn: nextPlayersTurn,
          isGameOver: false,
          chatMessages: game.chatMessages
        }
      end
    end
  end

  def clientViewOfShotsForPlayerTwo(game, playerName) do
    player1Won = checkIfPlayerOneWon(game)
    player2Won = checkIfPlayerTwoWon(game)

    if(player1Won || player2Won) do
      if(player1Won) do
        playerOneBoard = getPlayerOneBoardWithShotsAndShips(game)
        playerTwoBoard = getPlayerTwoBoardWithShotsAndShips(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "#{game.playerTwoName} has won!",
          currentPlayersTurn: "",
          isGameOver: true,
          chatMessages: game.chatMessages
        }
      else
        playerOneBoard = getPlayerOneBoardWithShotsAndShips(game)
        playerTwoBoard = getPlayerTwoBoardWithShotsAndShips(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "#{game.playerOneName} has won!",
          currentPlayersTurn: "",
          isGameOver: true,
          chatMessages: game.chatMessages
        }
      end
    else
      if(playerName == game.playerOneName) do
        nextPlayersTurn = game.playerTwoName
        playerOneBoard = getPlayerOneBoardWithShots(game)
        playerTwoBoard = getPlayerTwoBoardWithShotsAndShips(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "It is currently #{nextPlayersTurn}'s turn to attack",
          currentPlayersTurn: nextPlayersTurn,
          isGameOver: false,
          chatMessages: game.chatMessages
        }
      else
        nextPlayersTurn = game.playerOneName
        playerOneBoard = getPlayerOneBoardWithShots(game)
        playerTwoBoard = getPlayerTwoBoardWithShotsAndShips(game)
        %{
          playerOneBoardOfTiles: playerOneBoard,
          playerTwoBoardOfTiles: playerTwoBoard,
          playerOneName: game.playerOneName,
          playerTwoName: game.playerTwoName,
          playerOneReady: game.playerOneReady,
          playerTwoReady: game.playerTwoReady,
          attackPhase: game.attackPhase,
          globalMessage: "It is currently #{nextPlayersTurn}'s turn to attack",
          currentPlayersTurn: nextPlayersTurn,
          isGameOver: false,
          chatMessages: game.chatMessages
        }
      end
    end
  end

  def generateEmptyBoardOfTiles() do
    playerOneBoardOfTiles = []
    for x <- 0..numberOfTiles do
      playerOneBoardOfTiles = playerOneBoardOfTiles ++ false
    end
  end

  def numberOfTiles do
    length = 10
    width = 10;
    total = length * width - 1
  end

  def addPlayer(game, name) do
    cond do
      game.playerOneName == "" -> Map.put(game, :playerOneName, name)
      game.playerTwoName == "" -> Map.put(game, :playerTwoName, name)
    end
  end

  def checkIfTwoPlayersExist(game) do
    cond do
      game.playerOneName == "" -> false
      game.playerTwoName == "" -> false
      true -> true
    end
  end

  # -------- SHIP PLACEMENT -------- #
  # check if the ship will overflow beyond the column
  def outOfBound?(index, length, orientation) when orientation == "vertical" do
    index + (10 * (length - 1)) > 100
  end
  # check if the ship will overflow to the next line
  def outOfBound?(index, length, orientation) when orientation == "horizontal" do
    index + length > 100 || rem(index, 10) >= rem(index + length, 10) && rem(index + length, 10) != 0
  end

  # check if a ship has been placed in the proposed space
  def shipCollision?(game, index, length, orientation, playerName) when orientation == "vertical" do
    if(game.playerOneName == playerName) do
      shipIndices = calculateShipIndices(index, length, [], "vertical")
      Enum.any?(shipIndices, fn(x) ->
        MapSet.member?(game.playerOneIndicesOfShips, x)
      end)
    else
      shipIndices = calculateShipIndices(index, length, [], "vertical")
      Enum.any?(shipIndices, fn(x) ->
        MapSet.member?(game.playerTwoIndicesOfShips, x)
      end)
    end
  end

  # check if a ship has been placed in the proposed space
  def shipCollision?(game, index, length, orientation, playerName) when orientation == "horizontal" do
    if(game.playerOneName == playerName) do
      startIndex = index
      endIndex = index + length - 1
      Enum.any?(startIndex..endIndex, fn(x) ->
        MapSet.member?(game.playerOneIndicesOfShips, x)
      end)
    else
      startIndex = index
      endIndex = index + length - 1
      Enum.any?(startIndex..endIndex, fn(x) ->
        MapSet.member?(game.playerTwoIndicesOfShips, x)
      end)
    end
  end

  # get all indices of a ship
  defp calculateShipIndices(index, length, shipIndices, orientation) when length == 1, do: shipIndices ++ [index]
  defp calculateShipIndices(index, length, shipIndices, orientation) when orientation == "vertical" do
    shipIndices = shipIndices ++ [index]
    calculateShipIndices(index + 10, length - 1, shipIndices, orientation)
  end
  defp calculateShipIndices(index, length, shipIndices, orientation) when orientation == "horizontal" do
    shipIndices = shipIndices ++ [index]
    calculateShipIndices(index + 1, length - 1, shipIndices, orientation)
  end

  def addShip(game, index, length, orientation, playerName) when is_integer(length) do
    if(game.playerOneName == playerName) do
      shipIndices = calculateShipIndices(index, length, [], orientation)
      newPlayerOneIndicesOfShips = MapSet.new(shipIndices)
      allPlayerOneIndicesOfShip = MapSet.union(game.playerOneIndicesOfShips, newPlayerOneIndicesOfShips)
      Map.put(game, :playerOneIndicesOfShips, allPlayerOneIndicesOfShip)
    else
      shipIndices = calculateShipIndices(index, length, [], orientation)
      newPlayerTwoIndicesOfShips = MapSet.new(shipIndices)
      allPlayerTwoIndicesOfShip = MapSet.union(game.playerTwoIndicesOfShips, newPlayerTwoIndicesOfShips)
      Map.put(game, :playerTwoIndicesOfShips, allPlayerTwoIndicesOfShip)
    end
  end
  # --------- END SHIP PLACEMENT ---------- #

  def getPlayerOneBoard(game) do
    Enum.map(0..numberOfTiles, fn(x) ->
      cond do
        MapSet.member?(game.playerOneIndicesOfShips, x) ->
          "o"
        true ->
          false
      end
    end)
  end

  def getPlayerTwoBoard(game) do
    Enum.map(0..numberOfTiles, fn(x) ->
      cond do
        MapSet.member?(game.playerTwoIndicesOfShips, x) ->
          "o"
        true ->
          false
      end
    end)
  end

  def playerReady(game, playerName) do
    cond do
      game.playerOneName == playerName -> Map.put(game, :playerOneReady, true)
      game.playerTwoName == playerName -> Map.put(game, :playerTwoReady, true)
    end
  end

  def beginAttackPhase(game) do
    Map.put(game, :attackPhase, true)
  end

  def globalMessage(game, message) do
    Map.put(game, :globalMessage, message)
  end

  def attack(game, playerName, index) do
    #player 2 attacking player 1
    if(playerName != game.playerOneName) do
      newPlayerOneIndicesOfShots = MapSet.put(game.playerOneIndicesOfShots, index)
      Map.put(game, :playerOneIndicesOfShots, newPlayerOneIndicesOfShots)
    #player 1 attacking player 2
    else
      newPlayerTwoIndicesOfShots = MapSet.put(game.playerTwoIndicesOfShots, index)
      Map.put(game, :playerTwoIndicesOfShots, newPlayerTwoIndicesOfShots)
    end
  end

  def getPlayerOneBoardWithShots(game) do
    Enum.map(0..numberOfTiles, fn(x) ->
      cond do
        MapSet.member?(game.playerOneIndicesOfShips, x) && MapSet.member?(game.playerOneIndicesOfShots, x) ->
          "H"
        MapSet.member?(game.playerOneIndicesOfShots, x) ->
          "M"
        true ->
          false
      end
    end)
  end

  def getPlayerOneBoardWithShotsAndShips(game) do
    Enum.map(0..numberOfTiles, fn(x) ->
      cond do
        MapSet.member?(game.playerOneIndicesOfShips, x) && MapSet.member?(game.playerOneIndicesOfShots, x) ->
          "H"
        MapSet.member?(game.playerOneIndicesOfShots, x) ->
          "M"
        MapSet.member?(game.playerOneIndicesOfShips, x) ->
          "o"
        true ->
          false
      end
    end)
  end

  def getPlayerTwoBoardWithShots(game) do
    Enum.map(0..numberOfTiles, fn(x) ->
      cond do
        MapSet.member?(game.playerTwoIndicesOfShips, x) && MapSet.member?(game.playerTwoIndicesOfShots, x) ->
          "H"
        MapSet.member?(game.playerTwoIndicesOfShots, x) ->
          "M"
        true ->
          false
      end
    end)
  end

  def getPlayerTwoBoardWithShotsAndShips(game) do
    Enum.map(0..numberOfTiles, fn(x) ->
      cond do
        MapSet.member?(game.playerTwoIndicesOfShips, x) && MapSet.member?(game.playerTwoIndicesOfShots, x) ->
          "H"
        MapSet.member?(game.playerTwoIndicesOfShots, x) ->
          "M"
        MapSet.member?(game.playerTwoIndicesOfShips, x) ->
          "o"
        true ->
          false
      end
    end)
  end

  def checkIfPlayerOneWon(game) do
    cond do
      MapSet.subset?(game.playerOneIndicesOfShips, game.playerOneIndicesOfShots) ->
        true
      true ->
        false
    end
  end

  def checkIfPlayerTwoWon(game) do
    cond do
      MapSet.subset?(game.playerTwoIndicesOfShips, game.playerTwoIndicesOfShots) ->
        true
      true ->
        false
    end
  end

  def checkIfPlayerExists(game, playerName) do
    cond do
      game.playerOneName == playerName ->
        true
      game.playerTwoName == playerName ->
        true
      true ->
        false
    end
  end

  def addChatMessage(game, playerName, message) do
    newMessages = game.chatMessages ++ ["#{playerName}: #{message}"]
    Map.put(game, :chatMessages, newMessages)
  end

  def reset(game) do
    newBoard = generateEmptyBoardOfTiles()
    %{
      playerOneBoardOfTiles: newBoard,
      playerTwoBoardOfTiles: newBoard,
      playerOneName: game.playerOneName,
      playerTwoName: game.playerTwoName,
      playerOneIndicesOfShips: MapSet.new(),
      playerTwoIndicesOfShips: MapSet.new(),
      playerOneReady: false,
      playerTwoReady: false,
      attackPhase: false,
      globalMessage: "",
      playerOneIndicesOfShots: MapSet.new(),
      playerTwoIndicesOfShots: MapSet.new(),
      currentPlayersTurn: "",
      isGameOver: false,
      chatMessages: game.chatMessages
    }
  end
end
