defmodule Memory.Game do

  #initializes a fresh new game view model
  def initializeNewGame() do
    pairsOfLetters = generatePairsOfLetters()
    boardOfTiles = generateEmptyBoardOfTiles()
    viewModel = 
      %{
        pairsOfLetters: pairsOfLetters,
        boardOfTiles: boardOfTiles,
        indicesOfCorrectMatches: MapSet.new(),
        currentSelection: [],
        clickCount: 0,
        numberOfPairsMatchedCount: 0,
        gameWon: false
      }
  end

  #global variable for number of tiles
  def numberOfTiles do
    15
  end

  #grab all the pair of letters and shuffles them
  def generatePairsOfLetters() do
    letters = ["A", "B", "C", "D", "E", "F", "G", "H"]
    pairsOfLetters = letters ++ letters
    shuffledPairsOfLetters = Enum.shuffle(pairsOfLetters)
  end

  #creates an empty board model with all values set to false initially
  def generateEmptyBoardOfTiles() do
    boardOfTiles = []
    Enum.each(0..numberOfTiles, fn(x) ->
      boardOfTiles ++ false
    end)
  end

  #returns the client view model that gets sent to react code to be rendered
  def getClientViewModel(game) do
    boardOfTiles = getExistingBoard(game)
    viewModel = 
      %{
        boardOfTiles: boardOfTiles,
        clickCount: game.clickCount,
        numberOfPairsMatchedCount: game.numberOfPairsMatchedCount,
        gameWon: game.gameWon
      }
  end

  #reveal one tile
  def revealSingleTile(game, index) do
    boardOfTiles = generateBoardOneTile(game, index)
    viewModel = 
      %{
        boardOfTiles: boardOfTiles,
        clickCount: game.clickCount,
        numberOfPairsMatchedCount: game.numberOfPairsMatchedCount,
        gameWon: game.gameWon
      }
  end

  #helper for revealSingleTile()
  def generateBoardOneTile(game, index) do
    board =
      Enum.map(0..numberOfTiles, fn(x) ->
        #get already matched tiles
        if MapSet.member?(game.indicesOfCorrectMatches, x) do
          Enum.fetch(game.pairsOfLetters, x) 
            |> elem(1)
        else
          #match new tile
          if x == index do
            Enum.fetch(game.pairsOfLetters, x)
              |> elem(1)
          #no match, stay false
          else
            false
          end
        end
      end)
  end

  #get the existing board if it exists, else board of falses
  def getExistingBoard(game) do
    board =
      Enum.map(0..numberOfTiles, fn(x) ->
        if MapSet.member?(game.indicesOfCorrectMatches, x) do
          grabLetter(game, x)
        else
          false
        end
      end)
  end

  #helper to increment any count
  def incrementCount(count) do
    newCount = count + 1
  end

  #increment click count in this game
  def incrementClickCountInGame(game) do
    newClickCount = incrementCount(game.clickCount)
    Map.put(game, :clickCount, newClickCount)
  end

  #check if both tiles match
  def matchTiles(game, firstIndex, secondIndex) do
    #always want to grab the two letters, and new click count
    firstLetter = grabLetter(game, firstIndex)
    secondLetter = grabLetter(game, secondIndex)
    newClickCount = incrementCount(game.clickCount)
    
    #the new map we are returning
    newMap = game
    if firstLetter == secondLetter do
      newMatchedCount = incrementCount(game.numberOfPairsMatchedCount)
      indicesOfCorrectMatches = addIndicesToCollection(game, firstIndex, secondIndex)
      #check if game has been won yet
      if MapSet.size(indicesOfCorrectMatches) == 16 do
        newMap = Map.put(newMap, :indicesOfCorrectMatches, indicesOfCorrectMatches)
        newMap = Map.put(newMap, :clickCount, newClickCount)
        newMap = Map.put(newMap, :numberOfPairsMatchedCount, newMatchedCount)
        newMap = Map.put(newMap, :gameWon, true)
      else
        newMap = Map.put(newMap, :indicesOfCorrectMatches, indicesOfCorrectMatches)
        newMap = Map.put(newMap, :clickCount, newClickCount)
        newMap = Map.put(newMap, :numberOfPairsMatchedCount, newMatchedCount)
      end
    else
      newMap = Map.put(newMap, :clickCount, newClickCount)
    end
  end

  #get the letter at an index
  def grabLetter(game, index) do
    Enum.fetch(game.pairsOfLetters, index) |> elem(1)
  end

  #add indices to our collection of indices of correct matches
  def addIndicesToCollection(game, firstIndex, secondIndex) do
    indicesOfCorrectMatches = game.indicesOfCorrectMatches
    indicesOfCorrectMatches = MapSet.put(indicesOfCorrectMatches, firstIndex)
    indicesOfCorrectMatches = MapSet.put(indicesOfCorrectMatches, secondIndex)
  end

  #reveal both tiles provided
  def revealBothTiles(game, firstIndex, secondIndex) do
    boardOfTiles = generateBoardTwoTiles(game, firstIndex, secondIndex)
    viewModel = 
      %{
        boardOfTiles: boardOfTiles,
        clickCount: game.clickCount,
        numberOfPairsMatchedCount: game.numberOfPairsMatchedCount
      }
  end

  #helper for revealBothTiles
  def generateBoardTwoTiles(game, firstIndex, secondIndex) do
    board =
      Enum.map(0..numberOfTiles, fn(x) ->
        #get already matched tiles
        if MapSet.member?(game.indicesOfCorrectMatches, x) do
          grabLetter(game, x)
        else
          #match first tile?
          if x == firstIndex do
            grabLetter(game, firstIndex)
          else
            #match second tile?
            if x == secondIndex do
              grabLetter(game, secondIndex)
            #stay false
            else
              false
            end
          end
        end
      end)
  end
end
