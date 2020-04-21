import store from './store';

class TheServer {
    fetch_path(path, callback) {
        $.ajax(path, {
            method: "GET",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: "",
            success: callback,
        });
      }

    fetch_users() {
        this.fetch_path("/api/v1/users",
            (resp) => {
                store.dispatch({
                    type: 'GET_USER_LIST',
                    data: resp.data,
                });
            }
        );
    }

    fetch_tasks() {
        this.fetch_path("/api/v1/tasks",
            (resp) => {
                store.dispatch({
                    type: 'GET_TASK_LIST',
                    data: resp.data,
                });
            }
        );
    }
    
    send_post(path, data, successCallback, errorCallback) {
        $.ajax(path, {
            method: "POST",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(data),
            success: successCallback,
            error: errorCallback
        });
    }

    create_session(data) {
        $.ajax("/api/v1/sessions", {
            method: "POST",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(data),
            success: (resp) => {
                alert("Successfully logged in!");
                store.dispatch({
                    type: "NEW_SESSION",
                    session: resp.data,
                });
                store.dispatch({
                    type: "CLEAR_LOGIN_CREDENTIALS",
                    data: null
                });
            },
            error: () => {
                alert("Email and/or password incorrect...")
            }
        });
    }

    delete_task(id) {
        $.ajax("/api/v1/tasks/" + id, {
            method: "DELETE",
            success: (resp) => {
                alert("Successfully deleted task " + id);
            },
            error: (resp) => {
                alert("Failed to delete task " + id);
            }
        });
    }

    edit_task(id){
        $.ajax("/api/v1/tasks/" + id, {
          method: "GET",
          dataType: "json",
          contentType: "application/json; charset=UTF-8",
          success: (resp) => {
            let editTask = {
              title: resp.data.title,
              desc: resp.data.desc,
              time: resp.data.time,
              completed: resp.data.completed,
              id: resp.data.id,
              user_id: resp.data.user_id,
            };
            store.dispatch(
              {
                type: "EDIT_TASK",
                task: editTask,
              }
            );
          },
          error: (resp) => {
            alert("something is wrong, please try again")
          }
        });
    }

    make_edit_changes(data, id) {
        $.ajax("/api/v1/tasks/" + id, {
          method: "PUT",
          dataType: "json",
          contentType: "application/json; charset=UTF-8",
          data: JSON.stringify(data),
          success: (resp) => {
            alert("Changes successful!");
          },
          error: (resp) => {
            alert("something is wrong, please try again")
          }
        });
    }
}

export default new TheServer();