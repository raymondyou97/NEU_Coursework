import React from 'react';
import ReactDOM from 'react-dom';
import _ from 'lodash';

export default function game_init(root, channel) {
    ReactDOM.render(<Starter channel={channel}/>, root);
}

class Starter extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            boardOfTiles: [],
            clickCount: 0,
            numberOfPairsMatchedCount: 0,
            gameWon: false
        };

        this.channel = props.channel;
        this.currentSelection = -1;
        this.tilesClickable = true;
        this.joinChannel();
    }

    //update with view model returned from server
    returnViewModel(view) {
        this.setState(view.game);
    }

    //reset the game
    resetGame() {
        this.setTilesClickable();
        this.channel.push("resetGame")
            .receive("ok", this.returnViewModel.bind(this));
    }

    //found a match for two tiles
    matchTiles(view) {
        this.returnViewModel(view);
        this.setTilesUnclickable();
        setTimeout(function() {
            this.setTilesClickable();
            this.channel.push("getUpdate")
                .receive("ok", this.returnViewModel.bind(this));
        }.bind(this), 1000)
    }

    //reveal a tile with given index
    revealTile(index) {
        if (this.tilesClickable) { 
            if (this.currentSelection == -1) {
                this.currentSelection = index;
                this.channel.push("revealTile", {firstIndex: index})
                    .receive("ok", this.returnViewModel.bind(this));
            } else {
                this.channel.push("matchTiles", {firstIndex: this.currentSelection, secondIndex: index})
                    .receive("ok", this.matchTiles.bind(this));
                this.currentSelection = -1;
            }
        }
    }

    //flag for setting tiles unclickable
    setTilesUnclickable() {
        this.tilesClickable = false;
    }

    //set tiles clickable
    setTilesClickable() {
        this.tilesClickable = true;
    }

    //initially joining the channel
    joinChannel() {
        this.channel.join()
            .receive("ok", this.returnViewModel.bind(this))
            .receive("error", resp => {
                console.log("Unable to join channel. Called from starter-game.jsx", resp)
            });
    }

    render() {
        let tiles = [];
        for (let i = 0; i < this.state.boardOfTiles.length; i++) {
            tiles.push(<TileComponent key={i} attachOnClick={this.revealTile.bind(this)} letter={this.state.boardOfTiles[i]} index={i}/>);
        }

        return (
            <div className="game-container">
                <div className="title">
                    Memory Game
                </div>
                <div className="tile-row">
                    {tiles[0]}
                    {tiles[1]}
                    {tiles[2]}
                    {tiles[3]}
                </div>
                <div className="tile-row">
                    {tiles[4]}
                    {tiles[5]}
                    {tiles[6]}
                    {tiles[7]}
                </div>
                <div className="tile-row">
                    {tiles[8]}
                    {tiles[9]}
                    {tiles[10]}
                    {tiles[11]}
                </div>
                <div className="tile-row">
                    {tiles[12]}
                    {tiles[13]}
                    {tiles[14]}
                    {tiles[15]}
                </div>
                <div className="miscallaneous-container">
                    <div className="number-of-pairs-container">
                        # of Pairs Matched: {this.state.numberOfPairsMatchedCount}
                    </div>
                    <div className="click-count-container">
                        Current Click Count: {this.state.clickCount}
                    </div>
                    <div className="reset-btn-container">
                        <button onClick={this.resetGame.bind(this)}>
                            Reset
                        </button>
                    </div>
                </div>
                {
                    this.state.gameWon ? <div className="win-overlay"> "Congratz, you won!" </div> : null
                }
            </div>
        )
    }
}

function TileComponent(props) {
    if(props.letter) {
        return <div className="tile-container">
                    <span className="tile">
                        {props.letter}
                    </span>
                </div>
    }
    else {
        return <div className="tile-container" onClick={() => props.attachOnClick(props.index)}>
                    <span className="tile">
                        ?
                    </span>
                </div>
    }
}