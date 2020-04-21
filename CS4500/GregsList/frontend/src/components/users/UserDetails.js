import React, { Component } from 'react';
import UserService from '../../services/UserService';

import '../../styles/userDetails.css';

class UserDetails extends Component {
  constructor(props) {
    super(props);
    this.userService = UserService.getInstance();
    this.state = {
      id: this.props.match.params.id,
      users: [],
      username: '',
      firstName: '',
      lastName: '',
      password: '',
    };
  }

  componentDidMount() {
    this.userService.findAllUsers().then(users => {
      this.setState({
        users: users,
      });
    });
    this.selectUser(this.state.id);
  }

  updateUsername = e => {
    this.setState({ username: e.target.value });
  };

  updateFirstName = e => {
    this.setState({ firstName: e.target.value });
  };

  updateLastName = e => {
    this.setState({ lastName: e.target.value });
  };

  updatePassword = e => {
    this.setState({ password: e.target.value });
  };

  selectUser = id => {
    this.userService.findUserById(id).then(user => {
      this.props.history.push('/admin/users/' + id);
      this.setState({
        username: user.username,
        firstName: user.firstName,
        lastName: user.lastName,
        password: user.password,
      });
    });
  };

  backToUsers = () => {
    this.props.history.push('/admin/users/');
  };

  createUser = () => {
    const { username, firstName, lastName, password } = this.state;

    if (username && firstName && lastName && password) {
      this.userService
        .createUser({
          username,
          firstName,
          lastName,
          password,
        })
        .then(response => {
          this.props.history.push('/admin/users/');
        });
    }
  };

  deleteUser = id => {
    this.userService.deleteUser(id).then(response => {
      if (response.status === 200) {
        this.props.history.push('/admin/users/');
      } else {
        console.log(`Failed to delete user with id ${id}`);
      }
    });
  };

  updateUser = () => {
    const { id, firstName, lastName, username, password } = this.state;
    let userData = {
      id,
      firstName,
      lastName,
      username,
      password,
    };
    this.userService.updateUser(id, userData).then(response => {
      alert('User updated!');
    });
  };

  render() {
    return (
      <div className="user-detail-container">
        <h3 className="user-detail-username">{this.state.username}</h3>
        <span className="user-detail-row">
          <span className="user-detail-title">Users</span>
          <span className="user-detail-input">
            <select
              value={this.state.id}
              onChange={e => this.selectUser(e.target.value)}
              className="form-control"
            >
              {this.state.users.map(user => {
                return (
                  <option value={user.id} key={user.id}>
                    {user.username}
                  </option>
                );
              })}
            </select>
          </span>
        </span>
        <span className="user-detail-row">
          <span className="user-detail-title">Username</span>
          <span className="user-detail-input">
            <input
              onChange={this.updateUsername}
              className="form-control"
              value={this.state.username}
            />
          </span>
        </span>
        <span className="user-detail-row">
          <span className="user-detail-title">First Name</span>
          <span className="user-detail-input">
            <input
              onChange={this.updateFirstName}
              className="form-control"
              value={this.state.firstName}
            />
          </span>
        </span>
        <span className="user-detail-row">
          <span className="user-detail-title">Last Name</span>
          <span className="user-detail-input">
            <input
              onChange={this.updateLastName}
              className="form-control"
              value={this.state.lastName}
            />
          </span>
        </span>
        <span className="user-detail-row">
          <span className="user-detail-title">Last Name</span>
          <span className="user-detail-input">
            <input
              onChange={this.updatePassword}
              className="form-control"
              value={this.state.password}
            />
          </span>
        </span>
        <span className="user-detail-buttons">
          <button className="user-detail-cancel" onClick={this.backToUsers}>
            Cancel
          </button>
          <button
            className="user-detail-delete"
            onClick={() => this.deleteUser(this.state.id)}
          >
            Delete
          </button>
          <button className="user-detail-create" onClick={this.createUser}>
            Create
          </button>
          <button className="user-detail-update" onClick={this.updateUser}>
            Update
          </button>
        </span>
      </div>
    );
  }
}

export default UserDetails;
