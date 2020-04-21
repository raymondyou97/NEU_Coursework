import React from 'react';
import { connect } from 'react-redux';
import api from './api';
import _ from 'lodash';
import store from './store';

function NewTask(props) {
    function updateValue(event) {
        let newValue = $(event.target).val();
        let data;
        switch (event.target.name) {
            case "title":
                data = {
                    title: newValue
                };
                break;
            case "desc":
                data = {
                    desc: newValue
                };
                break;
            case "time":
                data = {
                    time: newValue
                };
                break;
            case "completed":
                data = {
                    completed: newValue
                };
                break;
            case "user_id":
                data = {
                    user_id: newValue
                };
                break;
        }
        props.dispatch({
            type: 'UPDATE_NEW_TASK_FORM',
            data: data
        });
    }

    function createNewTask(event) {
        event.preventDefault();
        if (props.form.time >= 0 && props.form.time % 15 == 0) {
            let data = {
                task: props.form
            };
            api.send_post("/api/v1/tasks", data,
                (resp) => {
                    alert("Successfully created new task!");
                    store.dispatch({
                        type: "CLEAR_TASK_FORM",
                        data: null,
                    });
                },
                (resp) => {
                    alert("Failed to create new task...");
                })
        }
        else {
            alert("Time worked on must be greater than or equal to 0 and a multiple of 15.");
        }
    }

    let allUser = [];
    for (let i = 0; i < props.users.length; i++) {
        allUser.push(props.users[i]);
    }
    let defaultOption;

    let allUserOptions = _.map(allUser, (user) => <option key={user.id} value={user.id}>{user.id} ({user.email})</option>);
    if(props.form.user_id) {
        defaultOption = <option key="-1"></option>;
    }
    else {
        defaultOption = <option key="-1" selected></option>;
    }
    allUserOptions = [defaultOption, ... allUserOptions];
    let UserOptions = <select name="user_id" onChange={() => updateValue(event)}>{allUserOptions}</select>

    return <div>
        <form>
            <div>
                <span className="new_task_column">Title:</span>
                <input type="text" name="title" value={props.form.title} onChange={() => updateValue(event)} />
            </div>
            <div>
                <span className="new_task_column">Description:</span>
                <input type="text" name="desc" value={props.form.desc} onChange={() => updateValue(event)} />
            </div>
            <div>
                <span className="new_task_column">Time worked on?:</span>
                <input type="number" name="time" min="0" step="15" value={props.form.time} onChange={() => updateValue(event)} />
            </div>
            <div>
                <span className="new_task_column">Completed:</span>
                <input type="checkbox" name="completed" value={props.form.completed} onChange={() => updateValue(event)} />
            </div>
            <div>
                <span className="new_task_column">Assigned To:</span>
                {UserOptions}
            </div>
            <button className="btn btn-primary" onClick={() => createNewTask(event)}>Create</button>
        </form>
    </div>;
}


function state2props(state) {
    return {
        form: state.form,
        users: state.users,
    };
}

export default connect(state2props)(NewTask);