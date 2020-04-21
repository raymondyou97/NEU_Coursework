import React from 'react';
import _ from 'lodash';

class TileComponent extends React.Component {
  constructor(props) {
    super(props);
  }

  render() {
    return (
      <div className={"tile-container " + (this.props.pairFound ? "pair-found" : "")} onClick={this.props.attachOnClick}>
              <span className="tile">
                {this.props.revealed ? this.props.letter : "?"}
            </span>
      </div>
    )
  }
}

export default TileComponent;
