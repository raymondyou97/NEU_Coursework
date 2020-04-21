import React from 'react';
import ReactDOM from 'react-dom';
import _ from 'lodash';
import $ from 'jquery';
import {
    BrowserRouter as Router,
    Route
} from 'react-router-dom';

import Header from './header';
import Homepage from './components/homepage';
import MyProfile from './components/myprofile';
import MyRecipes from './components/myrecipes';
import MyGroups from './components/mygroups';
import AllUsers from './components/allusers';
import AllGroups from './components/allgroups';
import AllUsersGroups from './components/allusersgroups';
import GroupChat from './components/group_chat';
import Groups from './components/groups';

export default function root_init(node) {
    ReactDOM.render(<Root />, node);
}

class Root extends React.Component {
    constructor(props) {
        super(props);
    }

    render() {
        return <Router>
            <Header history={this.props.history} />
            <Route exact path="/" component={Homepage} />
            <Route exact path="/users" component={AllUsers} />
            <Route exact path="/groups" component={AllGroups} />
            <Route exact path="/usersgroups" component={AllUsersGroups} />
            <Route exact path="/myprofile" component={MyProfile} />
            <Route exact path="/myrecipes" component={MyRecipes} />
            <Route exact path="/mygroups" component={MyGroups} />
            <Route exact path="/allgroups" component={Groups} />
            <GroupChat />
        </Router>
    }
}
