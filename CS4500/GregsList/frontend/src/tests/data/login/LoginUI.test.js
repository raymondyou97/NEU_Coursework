'use es6';

import React from 'react';
import Login from '../../../components/login/Login';

import { shallow } from 'enzyme';

test('DOM renders correctly without user data', () => {
  const component = shallow(
    <Login
      validateUser={() => {}}
      updateUsername={() => {}}
      updatePassword={() => {}}
      setError={() => {}}
      username={''}
      password={''}
      error={false}
    />
  );

  expect(component.find('.login-input').length).toEqual(2);
  expect(component.find('.username-input').props().value).toEqual('');
  expect(component.find('.password-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.login-label-fail').length).toEqual(0);
});

test('DOM renders correctly with user data', () => {
  const component = shallow(
    <Login
      validateUser={() => {}}
      updateUsername={() => {}}
      updatePassword={() => {}}
      setError={() => {}}
      username={'asdf'}
      password={'asdf'}
      error={false}
    />
  );

  expect(component.find('.login-input').length).toEqual(2);
  expect(component.find('.username-input').props().value).toEqual('asdf');
  expect(component.find('.password-input').props().value).toEqual('asdf');
  expect(component.find('.submit-button').props().disabled).toBe(false);
  expect(component.find('.login-label-fail').length).toEqual(0);
});

test('DOM renders correctly with user data and failed button', () => {
  const component = shallow(
    <Login
      validateUser={() => {}}
      updateUsername={() => {}}
      updatePassword={() => {}}
      setError={() => {}}
      username={'asdf'}
      password={'asdf'}
      error={true}
    />
  );

  expect(component.find('.login-input').length).toEqual(2);
  expect(component.find('.username-input').props().value).toEqual('asdf');
  expect(component.find('.password-input').props().value).toEqual('asdf');
  expect(component.find('.submit-button').props().disabled).toBe(false);
  expect(component.find('.login-label-fail').length).toEqual(1);
});
