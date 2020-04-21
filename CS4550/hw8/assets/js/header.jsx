import React from 'react';
import { Link } from 'react-router-dom';
import { connect } from 'react-redux';
import api from './api';

let LoginForm = connect(({login}) => {
    return {login};
})((props) => {
    function onChangeEmail(event) {
        let newValue = $(event.target).val();

        let data = {
            email: newValue
        };

        props.dispatch({
            type: 'UPDATE_LOGIN_CREDENTIALS',
            data: data,
        });
    }

    function onChangePassword(event) {
        let newValue = $(event.target).val();

        let data = {
            password: newValue
        };
        
        props.dispatch({
          type: 'UPDATE_LOGIN_CREDENTIALS',
          data: data,
        });
      }
    
    function login(event) {
        event.preventDefault();
        api.create_session(props.login);
    }

    function register(event) {
        event.preventDefault();
        let newUser = {
            user: {
                admin: false,
                email: props.login.email,
                password_hash: props.login.password
            }
        };

        api.send_post("/api/v1/users", newUser, 
        (data) => {
            alert("New user successfully created! Now log in...")
            window.location.reload();
        },
        (data) => {
            alert("Email already taken. Try Again!")
        });
    }

    let session_view = 
        <div className="form-inline my-2">
            <input id="login-email" type="email" placeholder="email" value={props.login.email} onChange={() => onChangeEmail(event)}/>
            <input id="login-pass" type="password" placeholder="password" value={props.login.password} onChange={() => onChangePassword(event)} />
            <button className="btn btn-success" onClick={() => login(event)}>Login</button>
            <button className="btn btn-danger" onClick={() => register(event)}>Register</button>
        </div>;

    return session_view;
});

let Session = connect(({session}) => {
    return {session};
})((props) => {
    function DELETE_SESSION() {
        props.dispatch({
            type: 'DELETE_SESSION'
        });
    }
    return <div className="navbar-text">
                <div>User: {props.session.email}</div>
                <button className="btn btn-danger" onClick={() => DELETE_SESSION()}>Log out</button>
            </div>;
});

function Header(props) {
    let session_info;
    if(props.session.token) {
        session_info = <Session session={props.token} />
    } else {
        session_info = <LoginForm />
    }

    return (
        <div className="row my-2">
            <div className="col-4">
                <h1>
                    <Link to={"/"}>Task Tracker</Link>
                </h1>
            </div>
            <div className="col-2">
                {props.session.token && 
                    <p>
                        <Link to={"/users"} onClick={() => api.fetch_users()}>All Users</Link>
                    </p>
                }
            </div>
            <div className="col-2">
                {props.session.token && 
                    <p>
                        <Link to={"/tasks"} onClick={() => api.fetch_tasks()}>All Tasks</Link>
                    </p>
                }
            </div>
            <div className="col-2">
                {props.session.token && 
                    <p>
                        <Link to={"/mytasks"} onClick={() => api.fetch_tasks()}>My Tasks</Link>
                    </p>
                }
                </div>
            <div className="col-2">
                {session_info}
            </div>
        </div>
    );
}
  
function state2props(state) {
    return {
        session: state.session,
    };
}

export default connect(state2props)(Header);