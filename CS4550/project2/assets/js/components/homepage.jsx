import React from 'react';
import _ from 'lodash';

class Homepage extends React.Component {
    constructor(props) {
        super(props);
    }

    render() {
        return (
            <div className="homepage-container">
                <h3 className="header-center">Welcome to FoodieFriends!</h3>
                <h5 className="header-center">Enjoy your stay!</h5>
                <img className="troll-img" src="/images/homepage.jpg"></img>
            </div>
        )
    }
}

export default Homepage;