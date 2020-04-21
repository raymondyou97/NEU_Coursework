defmodule Battleships.GameServer do
  use GenServer

  alias Battleships.Game
  alias Battleships.GameServer
  alias Battleships.GameSup
  alias Battleships.BackupAgent

  def reg(name) do
    {:via, Registry, {Battleships.GameReg, name}}
  end

  def start(name) do
    spec = %{
      id: __MODULE__,
      start: {__MODULE__, :start_link, [name]},
      restart: :permanent,
      type: :worker,
    }
    GameSup.start_child(spec)
  end

  def start_link(name) do
    game = BackupAgent.get(name) || Game.new()
    GenServer.start_link(__MODULE__, game, name: reg(name))
  end

  def addShip(name, index, length, orientation, playerName) do
    GenServer.call(reg(name), {:addShip, name, index, length, orientation, playerName})
  end

  def peek(name) do
    GenServer.call(reg(name), {:peek, name})
  end

  def addPlayer(gameName, playerName) do
    GenServer.call(reg(gameName), {:addPlayer, gameName, playerName})
  end

  def playerReady(gameName, playerName) do
    GenServer.call(reg(gameName), {:playerReady, gameName, playerName})
  end

  def beginAttackPhase(gameName) do
    GenServer.call(reg(gameName), {:beginAttackPhase, gameName})
  end

  def globalMessage(gameName, message) do
    GenServer.call(reg(gameName), {:globalMessage, gameName, message})
  end

  def attack(gameName, playerName, index) do
    GenServer.call(reg(gameName), {:attack, gameName, playerName, index})
  end

  def reset(gameName) do
    GenServer.call(reg(gameName), {:reset, gameName})
  end

  def chatMessage(gameName, playerName, message) do
    GenServer.call(reg(gameName), {:chatMessage, gameName, playerName, message})
  end

  def init(game) do
    terminateInFuture()
    {:ok, game}
  end

  def handle_call({:chatMessage, gameName, playerName, message}, _from, game) do
    game = Game.addChatMessage(game, playerName, message)
    {:reply, game, game}
  end

  def terminateInFuture do
    #900000 milliseconds = 15 minutes
    Process.send_after(self(), :terminateInFuture, 900000)
  end

  def handle_info(:terminateInFuture, game) do
    IO.puts("Terminating game as 15 minutes have passed...")
    {:stop, :normal, game}
  end

  def handle_call({:addShip, name, index, length, orientation, playerName}, _from, game) do
    try do
      game = Game.addShip(game, index, length, orientation, playerName)
      {:reply, game, game}
    rescue
      e in ArgumentError -> {:reply, game, game}
    end
  end

  def handle_call({:peek, name}, _from, game) do
    {:reply, game, game}
  end

  def handle_call({:addPlayer, gameName, playerName}, _from, game) do
    game = Game.addPlayer(game, playerName)
    {:reply, game, game}
  end

  def handle_call({:playerReady, gameName, playerName}, _from, game) do
    game = Game.playerReady(game, playerName)
    {:reply, game, game}
  end

  def handle_call({:beginAttackPhase, gameName}, _from, game) do
    game = Game.beginAttackPhase(game)
    {:reply, game, game}
  end

  def handle_call({:globalMessage, gameName, message}, _from, game) do
    game = Game.globalMessage(game, message)
    {:reply, game, game}
  end

  def handle_call({:attack, gameName, playerName, index}, _from, game) do
    game = Game.attack(game, playerName, index)
    {:reply, game, game}
  end

  def handle_call({:reset, gameName}, _from, game) do
    game = Game.reset(game)
    {:reply, game, game}
  end

end