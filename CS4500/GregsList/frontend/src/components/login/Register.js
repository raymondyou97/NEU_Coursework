'use es6';

import React, { PureComponent } from 'react';

import Button from 'react-bootstrap/Button';
import FormControl from 'react-bootstrap/FormControl';
import Form from 'react-bootstrap/Form';

import '../../styles/register.css';

class Register extends PureComponent {
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

  updateConfirmPassword = e => {
    this.props.updateConfirmPassword(e.target.value);
  };

  passwordsMatch = () => {
    return this.props.password === this.props.confirmPassword;
  };

  renderSubmit() {
    const {
      username,
      firstName,
      lastName,
      password,
      confirmPassword,
    } = this.props;

    const isButtonEnabled =
      username.length &&
      firstName.length &&
      lastName.length &&
      password.length &&
      confirmPassword.length &&
      this.passwordsMatch();

    return (
      <Button
        className="submit-button"
        disabled={!isButtonEnabled}
        onClick={this.props.createUser}
        variant="primary"
      >
        Register
      </Button>
    );
  }

  renderInputForms() {
    return (
      <Form>
        <Form.Label className="register-label">Username</Form.Label>
        <FormControl
          className="register-input username-input"
          onChange={this.updateUsername}
          placeholder="Username"
          value={this.props.username}
        />
        <Form.Label className="register-label">First name</Form.Label>
        <FormControl
          className="register-input firstname-input"
          onChange={this.updateFirstName}
          placeholder="First name"
          value={this.props.firstName}
        />
        <Form.Label className="register-label">Last name</Form.Label>
        <FormControl
          className="register-input lastname-input"
          onChange={this.updateLastName}
          placeholder="Last name"
          value={this.props.lastName}
        />
        <Form.Label className="register-label">Password</Form.Label>
        <FormControl
          className="register-input password-input"
          onChange={this.updatePassword}
          placeholder="Password"
          type="password"
          value={this.props.password}
        />
        <Form.Label className="register-label">Confirm password</Form.Label>
        <FormControl
          className={`register-input confirm-input ${
            this.passwordsMatch() ? '' : 'passwords-fail'
          }`}
          onChange={this.updateConfirmPassword}
          placeholder="Confirm password"
          type="password"
          value={this.props.confirmPassword}
        />
        {this.props.error ? (
          <Form.Label className="register-label-error">
            Username already exists
          </Form.Label>
        ) : null}
        {this.renderSubmit()}
      </Form>
    );
  }

  render() {
    return (
      <div className="register-container">
        <h1>Sign up</h1>
        {this.renderInputForms()}
      </div>
    );
  }
}

export default Register;
