import React, { Component } from 'react';

import '../../styles/users.css';

class Users extends Component {
  componentDidMount() {
    this.props.fetchUsers();
  }

  updateUsername = e => {
    this.props.updateUsername(e.target.value);
  };

  updateFirstName = e => {
    this.props.updateFirstName(e.target.value);
  };

  updateLastName = e => {
    this.props.updateLastName(e.target.value);
  };

  updatePassword = e => {
    this.props.updatePassword(e.target.value);
  };

  deleteUser = id => {
    this.props.deleteUser(id);
  };

  editUser = (id, username, firstName, lastName, password) => {
    this.props.selectUser(id);
    this.props.updateUsername(username);
    this.props.updateFirstName(firstName);
    this.props.updateLastName(lastName);
    this.props.updatePassword(password);
  };

  render() {
    const { selectedUser } = this.props;

    return (
      <div>
        <h3 className="user-title">Users</h3>
        <table className="user-table">
          <tbody className="user-table-body">
            {/* This is the name of the columns */}
            <tr className="user-columns">
              <td>Username</td>
              <td>First Name</td>
              <td>Last Name</td>
              <td>Password</td>
              <td></td>
            </tr>
            {/* This is the input fields for the columns */}
            <tr className="user-inputs">
              <td>
                <input
                  className="user-input-username"
                  type="text"
                  onChange={this.updateUsername}
                  placeholder="Username"
                  value={selectedUser.username}
                />
              </td>
              <td>
                <input
                  className="user-input-firstname"
                  type="text"
                  onChange={this.updateFirstName}
                  placeholder="First Name"
                  value={selectedUser.firstName}
                />
              </td>
              <td>
                <input
                  className="user-input-lastname"
                  type="text"
                  onChange={this.updateLastName}
                  placeholder="Last Name"
                  value={selectedUser.lastName}
                />
              </td>
              <td>
                <input
                  className="user-input-password"
                  type="text"
                  onChange={this.updatePassword}
                  placeholder="Password"
                  value={selectedUser.password}
                />
              </td>
              <td className="user-input-buttons">
                <button
                  className="user-add-button"
                  onClick={this.props.createUser}
                >
                  Add
                </button>
                <button
                  className="user-update-button"
                  onClick={this.props.updateUser}
                >
                  Update
                </button>
              </td>
            </tr>
            {/* This loops through the users */}
            {this.props.users.map(user => {
              const { id, username, firstName, lastName, password } = user;
              return (
                <tr className="user-details" key={id}>
                  <td onClick={() => this.props.showDetails(id)}>{username}</td>
                  <td onClick={() => this.props.showDetails(id)}>
                    {firstName}
                  </td>
                  <td onClick={() => this.props.showDetails(id)}>{lastName}</td>
                  <td onClick={() => this.props.showDetails(id)}>{password}</td>
                  <td className="user-buttons">
                    <button
                      className="user-delete-button"
                      onClick={() => this.deleteUser(id)}
                    >
                      Delete
                    </button>
                    <button
                      className="user-edit-button"
                      onClick={() =>
                        this.editUser(
                          id,
                          username,
                          firstName,
                          lastName,
                          password
                        )
                      }
                    >
                      Edit
                    </button>
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>
    );
  }
}

export default Users;
