'use es6';

import React, { PureComponent } from 'react';

import UserService from '../../services/UserService';
import Users from './Users';

class UsersContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.userService = UserService.getInstance();
    this.state = {
      selectedUser: -1,
      username: '',
      firstName: '',
      lastName: '',
      password: '',
      users: [],
    };
  }

  fetchUsers = () => {
    this.userService.findAllUsers().then(users => {
      this.setState({
        users: users,
      });
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

  updatePassword = password => {
    this.setState({ password });
  };

  selectUser = id => {
    this.setState({ selectedUser: id });
  };

  createUser = () => {
    const { username, firstName, lastName, password, users } = this.state;

    if (username && firstName && lastName && password) {
      this.userService
        .createUser({
          username,
          firstName,
          lastName,
          password,
        })
        .then(response => {
          this.setState({
            users: users.concat(response),
            username: '',
            firstName: '',
            lastName: '',
            password: '',
            selectedUser: -1,
          });
        });
    }
  };

  deleteUser = id => {
    this.userService.deleteUser(id).then(response => {
      if (response.status === 200) {
        const newUsers = this.state.users.filter(user => {
          return user.id !== id;
        });
        this.setState({ users: newUsers });
      } else {
        console.log(`Failed to delete user with id ${id}`);
      }
    });
  };

  editUser = (id, username, firstName, lastName, password) => {
    this.setState({
      selectedUser: id,
      username,
      firstName,
      lastName,
      password,
    });
  };

  updateUser = () => {
    const {
      selectedUser,
      firstName,
      lastName,
      username,
      password,
    } = this.state;
    if (selectedUser !== -1) {
      let userData = {
        id: selectedUser,
        firstName,
        lastName,
        username,
        password,
      };
      this.userService.updateUser(selectedUser, userData).then(response => {
        const newUsers = [];
        this.state.users.forEach(user => {
          if (user.id === selectedUser) {
            newUsers.push(userData);
          } else {
            newUsers.push(user);
          }
        });
        this.setState({
          users: newUsers,
          username: '',
          firstName: '',
          lastName: '',
          password: '',
          selectedUser: -1,
        });
      });
    }
  };

  showDetails = id => {
    this.props.history.push(`/admin/users/${id}`);
  };

  render() {
    const { firstName, lastName, username, password } = this.state;

    const selectedUser = {
      firstName,
      lastName,
      username,
      password,
    };

    return (
      <Users
        fetchUsers={this.fetchUsers}
        selectedUser={selectedUser}
        selectUser={this.selectUser}
        users={this.state.users}
        updateUsername={this.updateUsername}
        updateFirstName={this.updateFirstName}
        updateLastName={this.updateLastName}
        createUser={this.createUser}
        showDetails={this.showDetails}
        deleteUser={this.deleteUser}
        updateUser={this.updateUser}
        updatePassword={this.updatePassword}
      />
    );
  }
}

export default UsersContainer;
