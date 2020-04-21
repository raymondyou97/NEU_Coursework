'use es6';

import React, { PureComponent } from 'react';

import UserService from '../../services/UserService';
import Register from './Register';

class RegisterContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.userService = UserService.getInstance();
    this.state = {
      username: '',
      firstName: '',
      lastName: '',
      password: '',
      confirmPassword: '',
      error: false,
    };
  }

  updateUsername = username => {
    this.setState({ username });
  };

  updateFirstName = firstName => {
    this.setState({ firstName });
  };

  updateLastName = lastName => {
    this.setState({ lastName });
  };

  updatePassword = password => {
    this.setState({ password });
  };

  updateConfirmPassword = confirmPassword => {
    this.setState({ confirmPassword });
  };

  createUser = () => {
    const { username, firstName, lastName, password } = this.state;

    if (username && firstName && lastName && password) {
      this.userService.findUserByUsername(username).then(user => {
        if (user && user.username === username) {
          this.setState({ error: true });
        } else {
          this.userService
            .createUser({
              username,
              firstName,
              lastName,
              password,
            })
            .then(response => {
              localStorage.setItem('loggedInUser', username);
              window.location.replace('/');
            });
        }
      });
    }
  };

  render() {
    return (
      <Register
        firstName={this.state.firstName}
        lastName={this.state.lastName}
        username={this.state.username}
        password={this.state.password}
        confirmPassword={this.state.confirmPassword}
        updateUsername={this.updateUsername}
        updateFirstName={this.updateFirstName}
        updateLastName={this.updateLastName}
        updatePassword={this.updatePassword}
        updateConfirmPassword={this.updateConfirmPassword}
        createUser={this.createUser}
        error={this.state.error}
      />
    );
  }
}

export default RegisterContainer;
