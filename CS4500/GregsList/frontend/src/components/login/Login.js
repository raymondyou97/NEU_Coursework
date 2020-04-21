'use es6';

import React, { PureComponent } from 'react';

import Button from 'react-bootstrap/Button';
import FormControl from 'react-bootstrap/FormControl';
import Form from 'react-bootstrap/Form';

import '../../styles/login.css';

class Login extends PureComponent {
  updateUsername = e => {
    if (this.props.error) this.props.setError(false);
    this.props.updateUsername(e.target.value);
  };

  updatePassword = e => {
    if (this.props.error) this.props.setError(false);
    this.props.updatePassword(e.target.value);
  };

  loginUser = () => {
    this.props.validateUser();
  };

  renderSubmit() {
    const { username, password } = this.props;

    const isButtonEnabled = username.length && password.length;

    return (
      <Button
        className="submit-button"
        disabled={!isButtonEnabled}
        onClick={this.loginUser}
        variant="primary"
      >
        Log in
      </Button>
    );
  }

  renderInputForms() {
    const { error } = this.props;

    return (
      <Form>
        <Form.Label className="login-label">Username</Form.Label>
        <FormControl
          className={`login-input ${error ? 'error' : null} username-input`}
          onChange={this.updateUsername}
          placeholder="Username"
          value={this.props.username}
        />
        <Form.Label className="login-label">Password</Form.Label>
        <FormControl
          className={`login-input ${error ? 'error' : null} password-input`}
          onChange={this.updatePassword}
          placeholder="Password"
          type="password"
          value={this.props.password}
        />
        {error ? (
          <Form.Label className="login-label-fail">
            Username and password do not match!
          </Form.Label>
        ) : null}
        {this.renderSubmit()}
      </Form>
    );
  }

  render() {
    return (
      <div className="sign-in-container">
        <h1>Sign in</h1>
        {this.renderInputForms()}
      </div>
    );
  }
}

export default Login;
