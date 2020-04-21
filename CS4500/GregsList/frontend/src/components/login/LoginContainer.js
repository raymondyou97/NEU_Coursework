'use es6';

import React, { PureComponent } from 'react';

import UserService from '../../services/UserService';
import Login from './Login';

class LoginContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.userService = UserService.getInstance();
    this.state = {
      username: '',
      password: '',
      error: false,
      user: null,
    };
  }

  updateUsername = username => {
    this.setState({ username });
  };

  updatePassword = password => {
    this.setState({ password });
  };

  validateUser = () => {
    const { username, password } = this.state;
    this.userService.findUserByUsername(username).then(userData => {
      if (userData && userData.password === password) {
        localStorage.setItem('loggedInUser', username);
        localStorage.setItem('loggedInUserId', userData.id);
        window.location.replace('/');
      } else {
        this.setError(true);
      }
    });
  };

  setError = error => {
    this.setState({
      error,
    });
  };

  render() {
    return (
      <Login
        validateUser={this.validateUser}
        updateUsername={this.updateUsername}
        updatePassword={this.updatePassword}
        setError={this.setError}
        username={this.state.username}
        password={this.state.password}
        error={this.state.error}
      />
    );
  }
}

export default LoginContainer;
