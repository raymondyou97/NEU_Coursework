'use es6';

import React, { PureComponent } from 'react';

import UserService from '../../services/UserService';
import ProfileEdit from './ProfileEdit';

class ProfileEditContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.userService = UserService.getInstance();
    this.state = {
      id: '',
      username: '',
      firstName: '',
      lastName: '',
      oldPasswordCheck: '',
      oldPassword: '',
      newPassword: '',
      confirmNewPassword: '',
      nameError: false,
      oldPasswordError: false,
    };
  }

  fetchLoggedInUserInfo = () => {
    const user = localStorage.getItem('loggedInUser');
    if (user) {
      this.userService.findUserByUsername(user).then(foundUser => {
        if (foundUser) {
          this.setState({
            id: foundUser.id,
            username: foundUser.username,
            firstName: foundUser.firstName,
            lastName: foundUser.lastName,
            oldPasswordCheck: foundUser.password,
          });
        }
      });
    }
    this.setState({
      loggedInUser: user ? user : null,
    });
  };

  updateUsername = username => {
    this.setState({ username });
  };

  updateFirstName = firstName => {
    this.setState({ firstName });
  };

  updateLastName = lastName => {
    this.setState({ lastName });
  };

  updateOldPassword = oldPassword => {
    this.setState({ oldPassword });
  };

  updateNewPassword = newPassword => {
    this.setState({ newPassword });
  };

  updateConfirmNewPassword = confirmNewPassword => {
    this.setState({ confirmNewPassword });
  };

  updateUser = () => {
    const {
      id,
      username,
      firstName,
      lastName,
      oldPasswordCheck,
      oldPassword,
      newPassword,
    } = this.state;

    if (
      id &&
      username &&
      firstName &&
      lastName &&
      ((oldPassword && newPassword) || (!oldPassword && !newPassword))
    ) {
      this.userService.findUserByUsername(username).then(user => {
        console.log('Got to error checks');
        if (user && user.username === username && user.id !== id) {
          this.setState({ nameError: true });
        } else if (newPassword && oldPasswordCheck !== oldPassword) {
          this.setState({ oldPasswordError: true });
        } else {
          console.log('Updating User');
          this.userService
            .updateUser(
              id,
              newPassword
                ? {
                    username,
                    firstName,
                    lastName,
                    password: newPassword,
                  }
                : {
                    username,
                    firstName,
                    lastName,
                  }
            )
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
      <ProfileEdit
        firstName={this.state.firstName}
        lastName={this.state.lastName}
        username={this.state.username}
        oldPasswordCheck={this.state.oldPasswordCheck}
        oldPassword={this.state.oldPassword}
        newPassword={this.state.newPassword}
        confirmNewPassword={this.state.confirmNewPassword}
        fetchLoggedInUserInfo={this.fetchLoggedInUserInfo}
        updateUsername={this.updateUsername}
        updateFirstName={this.updateFirstName}
        updateLastName={this.updateLastName}
        updateOldPassword={this.updateOldPassword}
        updateNewPassword={this.updateNewPassword}
        updateConfirmNewPassword={this.updateConfirmNewPassword}
        updateUser={this.updateUser}
        nameError={this.state.nameError}
        oldPasswordError={this.state.oldPasswordError}
      />
    );
  }
}

export default ProfileEditContainer;
