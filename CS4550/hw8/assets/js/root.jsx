import React from 'react';
import ReactDOM from 'react-dom';
import _ from 'lodash';
import $ from 'jquery';
import { Link, BrowserRouter as Router, Route } from 'react-router-dom';

import Header from './header';
import UserList from './user_list';
import TaskList from './task_list';
import NewTask from './new_task';
import EditTask from './edit_task';
import MyTasks from './my_tasks';
import WelcomeScreen from  './welcome_screen';
import { Provider, connect } from 'react-redux';

import api from './api';

export default function root_init(node, store) {
    tasks = window.tasks;
    api.fetch_users();
    api.fetch_tasks();
    ReactDOM.render(<Provider store={store}>
                    <Root tasks={tasks} />
                    </Provider>, node);
}

let Root = connect((state) => state)((props) => {
    return <div>
                <Router>
                    <div>
                        <Header />
                        <div className="row">
                            <div className="col-10">
                                <Route path="/" exact={true} render={() =>
                                    <WelcomeScreen />
                                }/>
                                <Route path="/users" exact={true} render={() =>
                                    <UserList />
                                } />
                                <Route path="/tasks" exact={true} render={() =>
                                    <TaskList />
                                } />
                                <Route path="/mytasks" exact={true} render={() =>
                                    <MyTasks />
                                } />
                                <Route path="/tasks/new" exact={true} render={() =>
                                    <NewTask />
                                } />
                                <Route path="/tasks/edit/:id" exact={true} render={() =>
                                    <EditTask />
                                } />
                            </div>
                        </div>
                    </div>
                </Router>
            </div>;
});