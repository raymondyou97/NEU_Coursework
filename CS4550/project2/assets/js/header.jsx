import React from 'react';
import _ from 'lodash';
import { Link, BrowserRouter as Router, Route } from 'react-router-dom';
import RecipeSearch from './components/recipe_search';
import api from './utils/api';
import cookie_helper from './utils/cookie_helper';

class Header extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            email: "",
            password: "",
            loggedIn: false,
            admin: false
        };
    }

    componentDidMount() {
        let user_session = cookie_helper.getUserSession();
        if (user_session) {
            this.setState({
                email: user_session.email,
                password: "",
                loggedIn: true,
                admin: user_session.admin
            });
        }
    }

    updateInput(e) {
        switch (e.target.type) {
            case 'email':
                this.setState({
                    email: e.target.value
                });
                break;
            case 'password':
                this.setState({
                    password: e.target.value
                });
                break;
        }
    }

    login(e) {
        if (e === "click" || e.keyCode === 13) {
            let loginInfo = {
                email: this.state.email,
                password: this.state.password
            };

            api.login(loginInfo, (data) => {
                alert("Successfully logged in!");
                this.setState({
                    email: data.data.email,
                    password: "",
                    loggedIn: true,
                    admin: data.data.admin
                });
                location.reload();
            });
        }
    }

    logout() {
        cookie_helper.removeUserSession();
        this.setState({
            email: "",
            password: "",
            loggedIn: false,
            admin: false,
        });
        window.location = '/';
    }

    register() {
        let email = document.getElementById("email-input").value;
        let password = document.getElementById("password-input").value;
        let fname = document.getElementById("fname-input").value;
        let lname = document.getElementById("lname-input").value;
        let gender = document.getElementById("gender-input").value;
        let age = Number(document.getElementById("age-input").value);
        let newUser = {
            user: {
                email: email,
                password_hash: password,
                fname: fname,
                lname: lname,
                gender: gender,
                age: age,
                admin: false
            }
        };
        if (this.registerInputFormChecker(newUser.user)) {
            api.register(newUser, () => {
                alert("New user successfully created! Now log in...");
                $("#email-input").val('');
                $("#password-input").val('');
                $("#fname-input").val('');
                $("#lname-input").val('');
                $("#email-input").val('');
                $("#age-input").val('');
                $("#gender-input").val("default");
                $("#close-register-modal-btn").click();
            });
        }
    }

    registerInputFormChecker(user) {
        if (user) {
            if (user.email == "" || !user.email.includes("@")) {
                alert("Email empty/invalid");
                return false;
            }
            else if (user.password_hash === "") {
                alert("Password empty/invalid");
                return false;
            }
            else if (user.fname === "") {
                alert("First name empty/invalid");
                return false;
            }
            else if (user.lname === "") {
                alert("Last name empty/invalid");
                return false;
            }
            else if (user.gender === "default") {
                alert("gender invalid");
                return false;
            }
            else if (user.age === 0) {
                alert("age empty/invalid");
                return false;
            }
        }

        return true;
    }

    getLoginView() {
        let session_view;
        if (this.state.loggedIn) {
            session_view =
                <div className="form-inline my-2">
                    <span className="bold-text logged-in-text">Logged in as:</span>{this.state.email}
                    <div>
                        <button className="btn btn-success" onClick={() => this.logout()}>Logout</button>
                    </div>
                </div>;
        } else {
            session_view =
                <div className="form-inline my-2">
                    <div>
                        <input id="login-email" type="email" placeholder="email" onKeyDown={(e) => this.login(e)} onChange={(e) => this.updateInput(e)} />
                        <input id="login-pass" type="password" placeholder="password" onKeyDown={(e) => this.login(e)} onChange={(e) => this.updateInput(e)} />
                    </div>
                    <div>
                        <button className="btn btn-primary" onClick={() => this.login("click")}>Login</button>
                        <button className="btn btn-secondary" data-toggle="modal" data-target="#registerModal">Register</button>
                    </div>
                </div>;
        }

        return session_view;
    }

    menuOptions() {
        let menuOptions = [];
        //get admin options
        if (this.state.admin) {
            menuOptions.push(<div className="col-sm menu-option" key="0">
                <p>
                    <Link to={"/users"}>All Users (ADMIN)</Link>
                </p>
            </div>);
            menuOptions.push(<div className="col-sm menu-option" key="1">
                <p>
                    <Link to={"/groups"}>All Groups (ADMIN)</Link>
                </p>
            </div>);
            menuOptions.push(<div className="col-sm menu-option" key="2">
                <p>
                    <Link to={"/usersgroups"}>All UsersGroups (ADMIN)</Link>
                </p>
            </div>);
        }
        //get rest and return
        if (this.state.loggedIn) {
            menuOptions.push(<div className="col-sm menu-option" key="3">
                <p>
                    <Link to={"/myprofile"}>My Profile</Link>
                </p>
            </div>);
            menuOptions.push(<div className="col-sm menu-option" key="4">
                <p>
                    <Link to={"/myrecipes"}>My Recipes</Link>
                </p>
            </div>);
            menuOptions.push(<div className="col-sm menu-option" key="5">
                <p>
                    <Link to={"/mygroups"}>My Groups</Link>
                </p>
            </div>);
            menuOptions.push(<div className="col-sm menu-option" key="6">
                <p>
                    <Link to={"/allgroups"}>All Groups</Link>
                </p>
            </div>);

            return (
                <div className="row menu-option-container">
                    {menuOptions}
                </div>
            );
        }
    }

    displayRegisterModal() {
        return (
            <div className="modal fade" id="registerModal" tabIndex="-1" role="dialog">
                <div className="modal-dialog modal-dialog-centered" role="document">
                    <div className="modal-content">
                        <div className="modal-header">
                            <h3>Register new user</h3>
                        </div>
                        <div className="modal-body">
                            <div className="register-container">
                                <div className="input-group mb-3">
                                    <input type="text" className="form-control" id="email-input" placeholder="Email"></input>
                                </div>
                                <div className="input-group mb-3">
                                    <input type="password" className="form-control" id="password-input" placeholder="Password"></input>
                                </div>
                                <div className="input-group mb-3">
                                    <input type="text" className="form-control" id="fname-input" placeholder="First Name"></input>
                                </div>
                                <div className="input-group mb-3">
                                    <input type="text" className="form-control" id="lname-input" placeholder="Last Name"></input>
                                </div>
                                <div className="input-group mb-3">
                                    <select className="custom-select" id="gender-input">
                                        <option value="default" selected>Gender</option>
                                        <option value="male">Male</option>
                                        <option value="female">Female</option>
                                    </select>
                                </div>
                                <div className="input-group mb-3">
                                    <input type="number" className="form-control" id="age-input" placeholder="Age"></input>
                                </div>
                            </div>
                        </div>
                        <div className="modal-footer">
                            <button className="btn btn-success" onClick={() => this.register()}>Register</button>
                            <button id="close-register-modal-btn" type="button" className="btn btn-secondary" data-dismiss="modal">Close</button>
                        </div>
                    </div>
                </div>
            </div>
        )
    }

    render() {
        return (
            <div>
                <div className="row">
                    <div className="col-8">
                        <h1>
                            <Link to={"/"}>FoodieFriends</Link>
                        </h1>
                    </div>
                    <div className="col-4">
                        {this.getLoginView()}
                    </div>
                </div>
                {this.displayRegisterModal()}
                {this.menuOptions()}
                {this.state.loggedIn && <RecipeSearch />}
            </div>
        )
    }
}

export default Header;
