'use es6';

import React, { PureComponent } from 'react';

import Button from 'react-bootstrap/Button';
import FormControl from 'react-bootstrap/FormControl';
import Form from 'react-bootstrap/Form';

import '../../styles/profileEdit.css';

class ProfileEdit extends PureComponent {
  componentDidMount() {
    this.props.fetchLoggedInUserInfo();
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

  updateOldPassword = e => {
    this.props.updateOldPassword(e.target.value);
  };

  updateNewPassword = e => {
    this.props.updateNewPassword(e.target.value);
  };

  updateConfirmNewPassword = e => {
    this.props.updateConfirmNewPassword(e.target.value);
  };

  passwordsMatch = () => {
    return (
      (!this.props.oldPassword &&
        !this.props.newPassword &&
        !this.props.confirmNewPassword) ||
      this.props.newPassword === this.props.confirmNewPassword
    );
  };

  renderSubmit() {
    const {
      username,
      firstName,
      lastName,
      oldPassword,
      newPassword,
      confirmNewPassword,
    } = this.props;

    const isButtonEnabled =
      username.length &&
      firstName.length &&
      lastName.length &&
      ((oldPassword.length &&
        newPassword.length &&
        confirmNewPassword.length) ||
        (!oldPassword.length &&
          !newPassword.length &&
          !confirmNewPassword.length)) &&
      this.passwordsMatch();

    return (
      <Button
        className="submit-button"
        disabled={!isButtonEnabled}
        onClick={this.props.updateUser}
        variant="primary"
      >
        Update Information
      </Button>
    );
  }

  renderInputForms() {
    return (
      <Form>
        <Form.Label className="profile-edit-label">Username</Form.Label>
        <FormControl
          className="profile-edit-input username-input"
          onChange={this.updateUsername}
          placeholder="Username"
          value={this.props.username}
        />
        <Form.Label className="profile-edit-label">First name</Form.Label>
        <FormControl
          className="profile-edit-input firstname-input"
          onChange={this.updateFirstName}
          placeholder="First name"
          value={this.props.firstName}
        />
        <Form.Label className="profile-edit-label">Last name</Form.Label>
        <FormControl
          className="profile-edit-input lastname-input"
          onChange={this.updateLastName}
          placeholder="Last name"
          value={this.props.lastName}
        />
        <Form.Label className="profile-edit-label">Old password</Form.Label>
        <FormControl
          className="profile-edit-input password-input"
          onChange={this.updateOldPassword}
          placeholder="Old password"
          type="password"
          value={this.props.oldPassword}
        />
        <Form.Label className="profile-edit-label">New password</Form.Label>
        <FormControl
          className="profile-edit-input password-input"
          onChange={this.updateNewPassword}
          placeholder="New password"
          type="password"
          value={this.props.newPassword}
        />
        <Form.Label className="profile-edit-label">
          Confirm New password
        </Form.Label>
        <FormControl
          className={`profile-edit-input confirm-input ${
            this.passwordsMatch() ? '' : 'passwords-fail'
          }`}
          onChange={this.updateConfirmNewPassword}
          placeholder="Confirm password"
          type="password"
          value={this.props.confirmNewPassword}
        />
        {this.props.nameError ? (
          <Form.Label className="profile-edit-label-error">
            Username already exists
          </Form.Label>
        ) : null}
        {this.props.oldPasswordError ? (
          <Form.Label className="profile-edit-label-error">
            Old password is incorrect
          </Form.Label>
        ) : null}
        {this.renderSubmit()}
      </Form>
    );
  }

  render() {
    return (
      <div className="profile-edit-container">
        <h1>Edit My Profile</h1>
        {this.renderInputForms()}
      </div>
    );
  }
}

export default ProfileEdit;
