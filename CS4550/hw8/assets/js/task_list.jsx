import React from 'react';
import _ from 'lodash';
import { connect } from 'react-redux';
import { Link } from 'react-router-dom';
import Task from './task';

export default connect((state) => (state)) ((props) => {
    if(props.session.token && props.session.email) {
        let {root, tasks, dispatch} = props;
        let sortedTasks = _.orderBy(tasks, ['id'], ['asc']);
        let prods = _.map(sortedTasks, (task) =>
            <Task key={task.id} task={task} root={root} dispatch={dispatch}/>);
        return <div className="row">
                    <div className="new-task-btn">
                        <Link to={"tasks/new"} className="btn btn-outline-primary">New Task</Link>
                    </div>
                    {prods}
                </div>;
    } else {
        return <h3>Please login</h3>
    }
})