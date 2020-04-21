import React from 'react';
import ReactDOM from 'react-dom';
import _ from 'lodash';
import TileComponent from '../js/tile-component';

export default function game_init(root) {
    ReactDOM.render(<Starter />, root);
}

class Starter extends React.Component {
    constructor(props) {
        super(props);
        this.state = { 
            tiles: this.getAllPairsOfTiles(),
            currentSelection: [],
            currentIndexOfSelection: [],
            tilesClickable: true,
            clickCount: 0,
            numberOfPairsMatchedCount: 0,
            gameWon: false,
        };
    }

    getAllPairsOfTiles() {
        let letters = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'];
        let pairOfLetters = letters.concat(letters);
        let shuffledPairOfLetters = this.shuffle(pairOfLetters);
        let finalSetOfPairOfTiles = [];

        for (let i = 0; i < shuffledPairOfLetters.length; i++) {
            let letter = shuffledPairOfLetters[i];
            finalSetOfPairOfTiles.push(<TileComponent attachOnClick={() => this.revealTile(i, letter, true)} letter={letter} revealed={false}/>);
        }
        
        return finalSetOfPairOfTiles; 
    }

    //Shuffle algo taken from https://stackoverflow.com/a/6274398
    shuffle(array) {
        let counter = array.length;

        // While there are elements in the array
        while (counter > 0) {
            // Pick a random index
            let index = Math.floor(Math.random() * counter);

            // Decrease counter by 1
            counter--;

            // And swap the last element with it
            let temp = array[counter];
            array[counter] = array[index];
            array[index] = temp;
        }

        return array;
    }

    revealTile(index, letter, revealFlag) {
        //check if clicks are allowed
        if(this.state.tilesClickable) {
            //only reveal if its hidden
            if(revealFlag) {
                let currentLetters = this.state.currentSelection;
                let currentIndexOfSelection = this.state.currentIndexOfSelection;
                let currentTiles = this.state.tiles;
                let newTile = <TileComponent attachOnClick={() => this.revealTile(index, letter, false)} letter={letter} revealed={revealFlag ? true : false}/>;
                currentTiles[index] = newTile;
                this.setState({
                    tiles: currentTiles
                })
                //have first letter already, now see if second letter matches
                if(currentLetters.length == 1) {
                    let currentFirstLetter = currentLetters[0];
                    let currentFirstIndex = currentIndexOfSelection[0];
                    //check if the two letters match
                    if(currentFirstLetter !== letter) {
                        this.setTilesUnclickable();
                        setTimeout(function() {
                            this.hideTile(index, letter);
                            this.hideTile(currentFirstIndex, currentFirstLetter)
                            this.setTilesClickable();
                        }.bind(this), 1000)
                    }
                    //match found!
                    else {
                        this.addTileCompleteClass(index, letter);
                        this.addTileCompleteClass(currentFirstIndex, currentFirstLetter);
                        this.incrementNumberOfPairsMatchedCountAndCheckIfGameOver();
                    }
                    this.clearTileSelection();
                }
                //first letter here
                else {
                    this.addToSelection(index, letter);
                }
            }
            //already revealed, do nothing
            else {
                return;
            }

            this.incrementClickCount()
        }
    }

    addTileCompleteClass(index, letter) {
        let currentTiles = this.state.tiles;
        let newTile = <TileComponent pairFound={true} attachOnClick={() => this.revealTile(index, letter, false)} letter={letter} revealed={true}/>;
        currentTiles[index] = newTile;
        this.setState({
            tiles: currentTiles
        })
    }

    setTilesUnclickable() {
        this.setState( {
            tilesClickable: false
        });
    }

    setTilesClickable() {
        this.setState( {
            tilesClickable: true
        });
    }

    clearTileSelection() {
        this.setState( {
            currentSelection: [],
            currentIndexOfSelection: []
        });
    }

    clearEverything() {
        this.clearTileSelection();
        this.setState( {
            tiles: this.getAllPairsOfTiles(),
            tilesClickable: true,
            clickCount: 0,
            numberOfPairsMatchedCount: 0,
            gameWon: false,
        });
    }

    addToSelection(index, letter) {
        let selection = this.state.currentSelection;
        selection.push(letter);
        let indexOfSelection = this.state.currentIndexOfSelection;
        indexOfSelection.push(index);
        this.setState({
            currentSelection: selection,
            currentIndexOfSelection: indexOfSelection
        })
    }

    hideTile(index, letter) {
        let currentTiles = this.state.tiles;
        let newTile = <TileComponent attachOnClick={() => this.revealTile(index, letter, true)} letter={letter} revealed={false}/>;
        currentTiles[index] = newTile;
        this.setState({
            tiles: currentTiles
        })
    }

    incrementClickCount() {
        let currentClickCount = this.state.clickCount;
        this.setState( {
            clickCount: currentClickCount + 1
        });
    }

    incrementNumberOfPairsMatchedCountAndCheckIfGameOver() {
        let newNumberOfPairsMatchedCount = this.state.numberOfPairsMatchedCount + 1;
        this.setState( {
            numberOfPairsMatchedCount: newNumberOfPairsMatchedCount
        });

        //check if user has won yet
        if(newNumberOfPairsMatchedCount === 8) {
            this.setState( {
                gameWon: true
            });
        }
    }

    render() {
        return  <div className="game-container">
                    <div className="title">
                        Memory Game
                    </div>
                    <div className="tile-row">
                        {this.state.tiles[0]}
                        {this.state.tiles[1]}
                        {this.state.tiles[2]}
                        {this.state.tiles[3]}
                    </div>
                    <div className="tile-row">
                        {this.state.tiles[4]}
                        {this.state.tiles[5]}
                        {this.state.tiles[6]}
                        {this.state.tiles[7]}
                    </div>
                    <div className="tile-row">
                        {this.state.tiles[8]}
                        {this.state.tiles[9]}
                        {this.state.tiles[10]}
                        {this.state.tiles[11]}
                    </div>
                    <div className="tile-row">
                        {this.state.tiles[12]}
                        {this.state.tiles[13]}
                        {this.state.tiles[14]}
                        {this.state.tiles[15]}
                    </div>
                    <div className="miscallaneous-container">
                        <div className="number-of-pairs-container">
                        # of Pairs Matched: {this.state.numberOfPairsMatchedCount}
                        </div>
                        <div className="click-count-container">
                            Current Click Count: {this.state.clickCount}
                        </div>
                        <div className="reset-btn-container">
                            <button onClick={() => this.clearEverything()}>
                                Reset
                            </button>
                        </div>
                    </div>
                    {
                        this.state.gameWon ? <div className="win-overlay"> "Congratz, you won!" </div> : null
                    }
                </div>
    }
}