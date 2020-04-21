import React from 'react';
import ReactDOM from 'react-dom';
import _ from "lodash";

export default function battleships_init(root, channel) {
  ReactDOM.render(<Battleships channel={channel} />, root);
}

class Battleships extends React.Component {
  constructor(props) {
    super(props);

    this.state = {
      //shared and coming from server
      playerOneBoardOfTiles: [],
      playerTwoBoardOfTiles: [],
      playerOneName: "",
      playerTwoName: "",
      playerOneReady: false,
      playerTwoReady: false,
      playerOneMessage: "",
      playerTwoMessage: "",
      attackPhase: false,
      globalMessage: "",
      errorMessage: "",
      currentPlayersTurn: "",
      playerOneIsGameOver: false,
      playerTwoIsGameOver: false,
      resetCount: 0,
      chatMessages: [],

      //user specific stuff
      thisPlayerName: "",
      thisGameName: "",
      playerOneHoverIndices: [],
      playerTwoHoverIndices: [],
      playerOneHoverCollision: false,
      playerTwoHoverCollision: false,
      playerOneAttackHover: -1,
      playerTwoAttackhover: -1
    };
    this.channel = props.channel;

    this.joinChannel();
    this.getChannelListeners();
    this.getAllShips();
  }

  //initially joining the channel
  joinChannel() {
    this.channel
      .join()
      .receive("ok", resp => {
        this.getViewBeforeAttackPhase(resp);
        this.setState({
          thisPlayerName: resp.currentPlayerName
        })
      })
      .receive("error", resp => {
        console.log("Unable to join. ", resp.reason);
        this.setState({
          errorMessage: resp.reason
        })
      });
  }

  componentDidUpdate() {
    let messageBody = document.querySelector('#chat-msgs');
    messageBody.scrollTop = messageBody.scrollHeight - messageBody.clientHeight;
  }

  getChannelListeners() {
    this.channel.on('newPlayerHasJoined', (view) => {
      this.getViewBeforeAttackPhase(view);
    });

    this.channel.on('addShip', (view) => {
      this.getViewBeforeAttackPhase(view);
    });

    this.channel.on('reset', (view) => {
      let newCount = this.state.resetCount + 1;
      console.log(view);
      if(view.playerName == this.state.playerOneName) {
        this.setState({
          playerOneIsGameOver: false,
          resetCount: newCount
        });
      }
      else {
        this.setState({
          playerTwoIsGameOver: false,
          resetCount: newCount
        });
      }
      this.getViewBeforeAttackPhase(view);
    });

    this.channel.on('playerIsReady', (view) => {
      this.getViewBeforeAttackPhase(view);

      let whichPlayerAmI = view.currentPlayerName == this.state.playerOneName ? "1" : "2";
      //let other player know ur ready
      this.channel.push("globalMessage", { message: `Player ${whichPlayerAmI} (${view.currentPlayerName}) is ready!` })
        .receive("ok", resp => { this.getViewBeforeAttackPhase(resp); })

      //check if both players r ready
      if (this.state.playerOneReady && this.state.playerTwoReady) {
        this.channel.push("globalMessage", { message: `Attack phase has begun. It is currently ${this.state.playerOneName}'s turn to attack` })
          .receive("ok", resp => { this.getViewBeforeAttackPhase(resp) });
        //need to let both players know game is ready to start
        this.channel.push("beginAttackPhase", { playerName: this.state.playerOneName });
        this.channel.push("beginAttackPhase", { playerName: this.state.playerTwoName });
      }
    });

    this.channel.on('attackPhaseStarted', (view) => {
      this.getInitialAttackPhaseView(view);
    });

    this.channel.on('incomingGlobalMessage', (view) => {
      this.getViewBeforeAttackPhase(view);
    });

    this.channel.on("attackIncoming", (view) => {
      this.getViewDuringAttackPhase(view);
    });

    this.channel.on("newChatMessage", (view) => {
      this.setState({
        chatMessages: view.game.chatMessages
      });
    });
  }

  getAllShips() {
    //player one vars
    this.playerOneOrientation = "horizontal";
    this.playerOneShips = [2, 3, 3, 4, 5];
    this.playerOneShipSize = this.playerOneShips[0];
    this.playerOneShipsSet = false;
    this.playerOneShipHoverIndices = [];
    //player two vars
    this.playerTwoOrientation = "horizontal";
    this.playerTwoShips = [2, 3, 3, 4, 5];
    this.playerTwoShipSize = this.playerTwoShips[0];
    this.playerTwoShipsSet = false;
    this.playerTwoShipHoverIndices = [];
  }

  getViewBeforeAttackPhase(view) {
    this.setState(view.game);
    this.setState({
      thisGameName: view.gameName
    })
  }

  getInitialAttackPhaseView(view) {
    //only want view to be generated if its for you
    if (view.currentPlayerName == this.state.thisPlayerName) {
      if (this.state.thisPlayerName == this.state.playerOneName) {
        this.setState({
          playerOneBoardOfTiles: view.game.playerOneBoardOfTiles,
          playerTwoBoardOfTiles: view.game.playerTwoBoardOfTiles,
          currentPlayersTurn: view.game.currentPlayersTurn,
          globalMessage: view.game.globalMessage
        });
      }
      else {
        this.setState({
          playerOneBoardOfTiles: view.game.playerOneBoardOfTiles,
          playerTwoBoardOfTiles: view.game.playerTwoBoardOfTiles,
          currentPlayersTurn: view.game.currentPlayersTurn,
          globalMessage: view.game.globalMessage
        });
      }
    }
    this.setState({
      attackPhase: true
    });
  }

  getViewDuringAttackPhase(view) {
    if (this.state.thisPlayerName == this.state.playerOneName) {
      this.setState({
        playerOneBoardOfTiles: view.player1View.playerOneBoardOfTiles,
        playerTwoBoardOfTiles: view.player1View.playerTwoBoardOfTiles,
        currentPlayersTurn: view.player1View.currentPlayersTurn,
        globalMessage: view.player1View.globalMessage,
        playerOneIsGameOver: view.player1View.isGameOver,
        playerTwoIsGameOver: view.player1View.isGameOver
      })
    }
    else {
      this.setState({
        playerOneBoardOfTiles: view.player2View.playerOneBoardOfTiles,
        playerTwoBoardOfTiles: view.player2View.playerTwoBoardOfTiles,
        currentPlayersTurn: view.player2View.currentPlayersTurn,
        globalMessage: view.player2View.globalMessage,
        playerOneIsGameOver: view.player2View.isGameOver,
        playerTwoIsGameOver: view.player2View.isGameOver
      })
    }
  }

  addShip(incomingPlayerName, incomingIndex) {
    //only perform click your specific board
    if (incomingPlayerName != this.state.thisPlayerName) {
      return;
    }
    else {
      //player one
      if (this.state.thisPlayerName == this.state.playerOneName && !this.playerOneShipsSet && this.state.resetCount % 2 == 0) {
        this.channel.push("addShip", { playerName: incomingPlayerName, index: incomingIndex, length: this.playerOneShipSize, orientation: this.playerOneOrientation })
          .receive("ok", resp => {
            let shipIndex = this.playerOneShips.indexOf(this.playerOneShipSize);
            this.playerOneShips.splice(shipIndex, 1);
            this.playerOneShipsSet = this.playerOneShips.length == 0;
            this.playerOneShipSize = this.playerOneShips[0];
            this.setState({
              playerOneMessage: ""
            });
          })
          .receive("error", resp => {
            this.setState({
              playerOneMessage: resp.reason
            });
          });
      }
      //player two
      else if (this.state.thisPlayerName == this.state.playerTwoName && !this.playerTwoShipsSet && this.state.resetCount % 2 == 0) {
        this.channel.push("addShip", { playerName: incomingPlayerName, index: incomingIndex, length: this.playerTwoShipSize, orientation: this.playerTwoOrientation })
          .receive("ok", resp => {
            let shipIndex = this.playerTwoShips.indexOf(this.playerTwoShipSize);
            this.playerTwoShips.splice(shipIndex, 1);
            this.playerTwoShipsSet = this.playerTwoShips.length == 0;
            this.playerTwoShipSize = this.playerTwoShips[0];
            this.setState({
              playerTwoMessage: ""
            });
          })
          .receive("error", resp => {
            this.setState({
              playerTwoMessage: resp.reason
            });
          });
      }
    }
  }

  setOrientation(orientation) {
    if (this.state.thisPlayerName == this.state.playerOneName) {
      this.playerOneOrientation = orientation;
    }
    else {
      this.playerTwoOrientation = orientation;
    }
    this.forceUpdate();
  }

  setShipSize(size) {
    if (this.state.thisPlayerName == this.state.playerOneName) {
      this.playerOneShipSize = size;
    }
    else {
      this.playerTwoShipSize = size;
    }
    this.forceUpdate();
  }

  getShipSettingToolbar() {
    if (this.state.thisPlayerName == this.state.playerOneName) {
      return !this.playerOneShipsSet ?
        <div>
          {this.state.playerOneMessage && <div className="row player-msg">{this.state.playerOneMessage}</div>}
          <div className="row">
            <div className="column"><h5>Current Orientation: {this.playerOneOrientation}</h5></div>
            <div className="column"><h5>Current Ship Size: {this.playerOneShipSize}</h5></div>
          </div>
          <div className="row">
            <button className={this.playerOneOrientation == "vertical" ? "active-btn" : ""} onClick={this.setOrientation.bind(this, "vertical")}>Vertical</button>
            <button className={this.playerOneOrientation == "horizontal" ? "active-btn" : ""} onClick={this.setOrientation.bind(this, "horizontal")}>Horizontal</button>
          </div>
          <div className="row">{this.getShipButtons()}</div>
        </div> : null;
    }
    else {
      return !this.playerTwoShipsSet ?
        <div>
          {this.state.playerTwoMessage && <div className="row player-msg">{this.state.playerTwoMessage}</div>}
          <div className="row">
            <div className="column"><h5>Current Orientation: {this.playerTwoOrientation}</h5></div>
            <div className="column"><h5>Current Ship Size: {this.playerTwoShipSize}</h5></div>
          </div>
          <div className="row">
            <button className={this.playerTwoOrientation == "vertical" ? "active-btn" : ""} onClick={this.setOrientation.bind(this, "vertical")}>Vertical</button>
            <button className={this.playerTwoOrientation == "horizontal" ? "active-btn" : ""} onClick={this.setOrientation.bind(this, "horizontal")}>Horizontal</button>
          </div>
          <div className="row">{this.getShipButtons()}</div>
        </div> : null;
    }
  }

  getShipButtons() {
    if (this.state.thisPlayerName == this.state.playerOneName) {
      return this.playerOneShips.map((shipSize, i) =>
        <button key={i} className={this.playerOneShipSize == shipSize ? "active-btn" : ""} onClick={this.setShipSize.bind(this, shipSize)}>{shipSize}</button>
      )
    }
    else {
      return this.playerTwoShips.map((shipSize, i) =>
        <button key={i} className={this.playerTwoShipSize == shipSize ? "active-btn" : ""} onClick={this.setShipSize.bind(this, shipSize)}>{shipSize}</button>
      )
    }
  }

  playerReady(incomingPlayerName) {
    if (!this.state.playerOneReady || !this.state.playerTwoReady) {
      this.channel.push("playerReady", { playerName: incomingPlayerName })
    }
  }

  attack(incomingPlayerName, incomingIndex) {
    if (incomingPlayerName == this.state.thisPlayerName && this.state.thisPlayerName == this.state.currentPlayersTurn) {
      this.channel.push("attack", { playerName: incomingPlayerName, index: incomingIndex })
        .receive("ok", resp => {
          this.getViewDuringAttackPhase(resp);
        })
        .receive("error", resp => {
          console.log(resp);
        })
    }
  }

  shipPreview(index, toggleFlag) {
    if (toggleFlag) {
      //player one
      if (this.state.thisPlayerName == this.state.playerOneName) {
        let arrayOfIndices = [index];
        if (this.playerOneOrientation == "horizontal") {
          let count = 1;
          let row = Math.floor((index / 10)) + 1;
          while (count < this.playerOneShipSize && (index + count) / (row * 10) < 1) {
            if(this.state.playerOneBoardOfTiles[index + count]) {
              break;
            }
            arrayOfIndices.push(index + count);
            count++;
          }
        }
        else {
          let increment = 10;
          let max = increment * this.playerOneShipSize;
          while (increment < max && index + increment < 100) {
            if(this.state.playerOneBoardOfTiles[index + increment]) {
              break;
            }
            arrayOfIndices.push(index + increment);
            increment += 10;
          }
        }
        let hoverCollision = arrayOfIndices.length == this.playerOneShipSize ? true : false;
        this.setState({
          playerOneHoverIndices: arrayOfIndices,
          playerOneHoverCollision: hoverCollision
        });
      }
      //player two
      else {
        let arrayOfIndices = [index];
        if (this.playerTwoOrientation == "horizontal") {
          let count = 1;
          let row = Math.floor((index / 10)) + 1;
          while (count < this.playerTwoShipSize && (index + count) / (row * 10) < 1) {
            if(this.state.playerTwoBoardOfTiles[index + count]) {
              break;
            }
            arrayOfIndices.push(index + count);
            count++;
          }
        }
        else {
          let increment = 10;
          let max = increment * this.playerTwoShipSize;
          while (increment < max && index + increment < 100) {
            if(this.state.playerTwoBoardOfTiles[index + increment]) {
              break;
            }
            arrayOfIndices.push(index + increment);
            increment += 10;
          }
        }
        let hoverCollision = arrayOfIndices.length == this.playerTwoShipSize ? true : false;
        this.setState({
          playerTwoHoverIndices: arrayOfIndices,
          playerTwoHoverCollision: hoverCollision
        });
      }
    }
    else {
      this.setState({
        playerOneHoverIndices: [],
        playerTwoHoverIndices: []
      });
    }
  }

  resetGame() {
    this.channel.push("reset");
    if (this.state.resetCount % 2 == 0) {
      this.channel.push("globalMessage", { message: `${this.state.thisPlayerName} wants to play again! Waiting for opponent...` })
      .receive("ok", resp => { this.getViewBeforeAttackPhase(resp) });
    } else {
      this.channel.push("globalMessage", { message: `New game started.` })
      .receive("ok", resp => { this.getViewBeforeAttackPhase(resp) });
    }

    //player one vars
    this.playerOneShips = [2, 3, 3, 4, 5];
    this.playerOneShipSize = this.playerOneShips[0];
    this.playerOneShipsSet = false;
    //player two vars
    this.playerTwoShips = [2, 3, 3, 4, 5];
    this.playerTwoShipSize = this.playerTwoShips[0];
    this.playerTwoShipsSet = false;
    this.forceUpdate();
  }

  sendMessage(event) {
    if (event.key === 'Enter') {
      let message = event.target.value;
      if (message) {
        this.channel.push("chatMessage", { playerName: this.state.thisPlayerName, message: message });
        document.getElementById("message-input").value = "";
      }
    }
  }

  attackPreviewForPlayerOne(index, toggleFlag) {
    if(toggleFlag) {
      if(this.state.thisPlayerName == this.state.playerOneName) {
        this.setState({
          playerOneAttackHover: index
        });
      }
    }
    else {
      this.setState({
        playerOneAttackHover: -1
      });
    }
  }

  attackPreviewForPlayerTwo(index, toggleFlag) {
    if(toggleFlag) {
      if(this.state.thisPlayerName == this.state.playerTwoName) {
        this.setState({
          playerTwoAttackHover: index
        });
      }
    }
    else {
      this.setState({
        playerTwoAttackHover: -1
      });
    }
  }

  getPlayerOneBoard() {
    let playerOneTiles = [];
    let playerOneHoverClasses = "";
    if (this.state.attackPhase) {
      for (let i = 0; i < this.state.playerOneBoardOfTiles.length; i++) {
        playerOneTiles.push(<Tile
          key={i}
          className={this.state.playerTwoAttackHover == i ? "ship-preview-attack" : ""}
          attachOnMouseOver={() => this.attackPreviewForPlayerTwo(i, true)}
          attachOnMouseOut={() => this.attackPreviewForPlayerTwo(0, false)}
          attachOnClick={() => this.attack(this.state.playerTwoName, i)}
          letter={this.state.playerOneBoardOfTiles[i]} index={i} />);
      }
    }
    else {
      for (let i = 0; i < this.state.playerOneBoardOfTiles.length; i++) {
        if (this.state.playerOneHoverIndices.includes(i) && this.state.playerOneHoverCollision) {
          playerOneHoverClasses = "ship-preview";
        }
        else if (this.state.playerOneHoverIndices.includes(i)) {
          playerOneHoverClasses = "ship-preview-collision";
        }
        else {
          playerOneHoverClasses = "";
        }
        playerOneTiles.push(<Tile
          key={i}
          className={playerOneHoverClasses}
          attachOnMouseOver={() => this.shipPreview(i, true)}
          attachOnMouseOut={() => this.shipPreview(0, false)}
          attachOnClick={() => this.addShip(this.state.playerOneName, i)}
          letter={this.state.playerOneBoardOfTiles[i]} index={i} />);
      }
    }

    let tileRows = _.chunk(playerOneTiles, 10);

    let playerOneFinalBoard = [];
    for (let i = 0; i < tileRows.length; i++) {
      playerOneFinalBoard.push(<div key={i} className="tile-row">{tileRows[i]}</div>);
    }
    return playerOneFinalBoard;
  }

  getPlayerTwoBoard() {
    let playerTwoTiles = [];
    let playerTwoHoverClasses = "";
    if (this.state.attackPhase) {
      for (let i = 0; i < this.state.playerTwoBoardOfTiles.length; i++) {
        playerTwoTiles.push(<Tile
          key={i}
          className={this.state.playerOneAttackHover == i ? "ship-preview-attack" : ""}
          attachOnMouseOver={() => this.attackPreviewForPlayerOne(i, true)}
          attachOnMouseOut={() => this.attackPreviewForPlayerOne(0, false)}
          attachOnClick={() => this.attack(this.state.playerOneName, i)}
          letter={this.state.playerTwoBoardOfTiles[i]} index={i} />);
      }
    }
    else {
      for (let i = 0; i < this.state.playerTwoBoardOfTiles.length; i++) {
        if (this.state.playerTwoHoverIndices.includes(i) && this.state.playerTwoHoverCollision) {
          playerTwoHoverClasses = "ship-preview";
        }
        else if (this.state.playerTwoHoverIndices.includes(i)) {
          playerTwoHoverClasses = "ship-preview-collision";
        }
        else {
          playerTwoHoverClasses = "";
        }
        playerTwoTiles.push(<Tile
          key={i}
          className={playerTwoHoverClasses}
          attachOnMouseOver={() => this.shipPreview(i, true)}
          attachOnMouseOut={() => this.shipPreview(0, false)}
          attachOnClick={() => this.addShip(this.state.playerTwoName, i)}
          letter={this.state.playerTwoBoardOfTiles[i]} index={i} />);
      }
    }

    let tileRows = _.chunk(playerTwoTiles, 10);

    let playerTwoFinalBoard = [];
    for (let i = 0; i < tileRows.length; i++) {
      playerTwoFinalBoard.push(<div key={i} className="tile-row">{tileRows[i]}</div>);
    }

    return playerTwoFinalBoard;
  }

  getChatMessages() {
    let chatMessages = [];
    for (let i = 0; i < this.state.chatMessages.length; i++) {
      let wholeMessage = this.state.chatMessages[i].split(": ");
      let sender = wholeMessage[0];
      let message = wholeMessage[1];
      let spanMsg;
      if(this.state.thisPlayerName == sender) {
        spanMsg = <span className="msg-sender friendly">{sender}: </span>
      }
      else {
        spanMsg = <span className="msg-sender enemy">{sender}: </span>
      }
      chatMessages.push(<li key={i} className="msg">
        {spanMsg}
        <span>{message}</span>
      </li>)
    }

    return chatMessages;
  }

  render() {
    let playerOneFinalBoard = this.getPlayerOneBoard();
    let playerTwoFinalBoard = this.getPlayerTwoBoard();

    let playerOneReadyButton = this.playerOneShipsSet && !this.state.attackPhase ? <button className={"ready-btn " + (this.state.playerOneReady ? "disable-btn" : "")} onClick={() => this.playerReady(this.state.playerOneName)}>Ready to play</button> : null;
    let playerTwoReadyButton = this.playerTwoShipsSet && !this.state.attackPhase ? <button className={"ready-btn " + (this.state.playerTwoReady ? "disable-btn" : "")} onClick={() => this.playerReady(this.state.playerTwoName)}>Ready to play</button> : null;

    let player1Indicator = "";
    let player2Indicator = "";
    let whichPlayerAmI = 0;
    if (this.state.playerOneName != "") {
      player1Indicator = this.state.thisPlayerName == this.state.playerOneName ? "(YOU)" : "(ENEMY)";
      whichPlayerAmI = this.state.thisPlayerName == this.state.playerOneName ? 1 : whichPlayerAmI;
    }
    if (this.state.playerTwoName != "") {
      player2Indicator = this.state.thisPlayerName == this.state.playerTwoName ? "(YOU)" : "(ENEMY)";
      whichPlayerAmI = this.state.thisPlayerName == this.state.playerTwoName ? 2 : whichPlayerAmI;
    }

    if (this.state.thisPlayerName == this.state.playerOneName) {
      var playerOneShipSettingToolbar = this.getShipSettingToolbar();
    }
    else {
      var playerTwoShipSettingToolbar = this.getShipSettingToolbar();
    }

    let chatMessages = this.getChatMessages();

    return (
      <div className="whole-container">
        {!this.state.errorMessage &&
          <div>
            <div className="personal-container">
              <h1 className="title-battleships">Battleships</h1>
              <p>Current Game Name: {this.state.thisGameName}</p>
              <p>Current Player Name: {this.state.thisPlayerName}</p>
            </div>
            <div className="tile-container">
              <div className="board-container left-board">
                <p className={"player-text " + (whichPlayerAmI == 1 ? "friendly" : "enemy")}>
                  Player 1: {this.state.playerOneName} {player1Indicator}
                </p>
                <div className={"board-and-btns " + (whichPlayerAmI !== 1 && !this.state.attackPhase ? "toggle-display" : "")}>
                  {playerOneFinalBoard}
                  {playerOneShipSettingToolbar}
                  {playerOneReadyButton}
                </div>
                <div className={"waiting-text " + (whichPlayerAmI == 1 || this.state.attackPhase ? "toggle-display" : "")}>
                  Waiting for player to be ready...
                </div>
              </div>
              <div className="board-container">
                <p className={"player-text " + (whichPlayerAmI == 2 ? "friendly" : "enemy")}>
                  Player 2: {this.state.playerTwoName} {player2Indicator}
                </p>
                <div className={"board-and-btns " + (whichPlayerAmI !== 2 && !this.state.attackPhase ? "toggle-display" : "")}>
                  {playerTwoFinalBoard}
                  {playerTwoShipSettingToolbar}
                  {playerTwoReadyButton}
                </div>
                <div className={"waiting-text " + (whichPlayerAmI == 2 || this.state.attackPhase ? "toggle-display" : "")}>
                  Waiting for player to be ready...
                </div>
              </div>
              <div className="chat-container">
                <p className="chat-room-title">
                  Chat Room:
                </p>
                <div className="chat-messages">
                  <ul id="chat-msgs" className="chat-messages-2">
                    {chatMessages}
                  </ul>
                </div>
                <input onKeyPress={(event) => this.sendMessage(event)} type="text" id="message-input" class="message-input-box form-control" placeholder="Chat here!"></input>
              </div>
            </div>
          </div>
        }
        {this.state.globalMessage &&
          <p className="global-msg">
            Global Game Message: {this.state.globalMessage}
          </p>
        }
        {this.state.playerOneIsGameOver && this.state.thisPlayerName == this.state.playerOneName &&
          <div className="play-again">
            <button onClick={() => this.resetGame()}> Play Again! </button>
          </div>
        }
        {this.state.playerTwoIsGameOver && this.state.thisPlayerName == this.state.playerTwoName &&
          <div className="play-again">
            <button onClick={() => this.resetGame()}> Play Again! </button>
          </div>
        }
        {this.state.errorMessage &&
          <p className="error-message">
            {this.state.errorMessage}
          </p>
        }
      </div>
    );
  }
}

function Tile(props) {
  if (props.letter == "o") {
    return <span className="tile">
      <img src="https://i.imgur.com/s3u1M11.png"></img>
    </span>
  }
  else if (props.letter == "H") {
    return <span className="tile">
      <img src="https://i.imgur.com/l1JTdod.png"></img>
    </span>
  }
  else if (props.letter == "M") {
    return <span className="tile">
      <img src="https://i.imgur.com/wDvNKOA.jpg"></img>
    </span>
  }
  else {
    return <span className={"tile " + props.className}
      onClick={() => props.attachOnClick(props.index)}
      onMouseOver={() => props.attachOnMouseOver(props.index)}
      onMouseOut={() => props.attachOnMouseOut(props.index)}>
    </span>
  }
}