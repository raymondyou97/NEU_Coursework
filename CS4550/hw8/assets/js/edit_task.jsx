import React from 'react';
import { connect } from 'react-redux';
import api from './api';
import _ from 'lodash';

function EditTask(props) {
    function updateValue(event) {
        let newValue = $(event.target).val();
        let data;
        switch(event.target.name) {
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
                newValue = $(event.target).prop("checked");
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
            type: 'UPDATE_TASK',
            data: data
        });
    }

    function editTask(event) {
        event.preventDefault();
        if(props.edit_task_form.time >= 0 && props.edit_task_form.time % 15 == 0) {
            let editedTask = {
                task: {
                    title: props.edit_task_form.title,
                    desc: props.edit_task_form.desc,
                    time: props.edit_task_form.time,
                    completed: props.edit_task_form.completed
                }
            };
            api.make_edit_changes(editedTask, props.edit_task_form.id);
        }
        else {
            alert("Time worked on must be greater than or equal to 0 and a multiple of 15.");
        }
    }

    return <div>
                <form>
                    <div>
                        <span className="new_task_column">Title:</span>
                        <input type="text" name="title" value={props.edit_task_form.title} onChange={() => updateValue(event)}/>
                    </div>
                    <div>
                        <span className="new_task_column">Description:</span>
                        <input type="text" name="desc" value={props.edit_task_form.desc} onChange={() => updateValue(event)}/>
                    </div>
                    <div>
                        <span className="new_task_column">Time worked on?:</span>
                        <input type="number" name="time" min="0" step="15" value={props.edit_task_form.time} onChange={() => updateValue(event)}/>
                    </div>
                    <div>
                        <span className="new_task_column">Completed:</span>
                        <input type="checkbox" name="completed" checked={props.edit_task_form.completed} onChange={() => updateValue(event)}/>
                    </div>
                    <div>
                        <span className="new_task_column">Assigned To:</span>
                        <input type="text" name="user_id" value={props.edit_task_form.user_id} onChange={() => updateValue(event)} />
                    </div>
                    <button className="btn btn-primary" onClick={() => editTask(event)}>Submit Changes</button>
                </form>
            </div>;
}


function state2props(state) {
    return {
        edit_task_form: state.edit_task_form,
        users: state.users,
    };
}

export default connect(state2props)(EditTask);