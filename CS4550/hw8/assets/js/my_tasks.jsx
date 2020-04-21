import React from 'react';
import _ from 'lodash';
import { connect } from 'react-redux';
import Task from './task';

export default connect((state) => (state)) ((props) => {
    let {root, tasks, dispatch} = props;

    let myUserID = props.session.user_id;
    let sortedTasks = _.orderBy(tasks, ['id'], ['asc']);
    let mySortedTasks = _.filter(sortedTasks, {
        user_id: myUserID
    });
    let prods = _.map(mySortedTasks, (task) => 
        <Task key={task.id} task={task} root={root} dispatch={dispatch}/>);

    return <div className="row">
                {prods}
            </div>;
})