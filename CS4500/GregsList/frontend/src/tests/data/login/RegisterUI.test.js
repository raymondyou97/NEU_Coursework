'use es6';

import React from 'react';
import Register from '../../../components/login/Register';

import { shallow } from 'enzyme';

test('DOM renders correctly without user data', () => {
  const component = shallow(
    <Register
      firstName={''}
      lastName={''}
      username={''}
      password={''}
      confirmPassword={''}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updatePassword={() => {}}
      updateConfirmPassword={() => {}}
      createUser={() => {}}
    />
  );

  expect(component.find('.register-input').length).toEqual(5);
  expect(component.find('.username-input').props().value).toEqual('');
  expect(component.find('.firstname-input').props().value).toEqual('');
  expect(component.find('.lastname-input').props().value).toEqual('');
  expect(component.find('.password-input').props().value).toEqual('');
  expect(component.find('.confirm-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(0);
});

test('DOM renders correctly with some user data', () => {
  const component = shallow(
    <Register
      firstName={'asdf'}
      lastName={'asdf'}
      username={'asdf'}
      password={'asdf'}
      confirmPassword={''}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updatePassword={() => {}}
      updateConfirmPassword={() => {}}
      createUser={() => {}}
    />
  );

  expect(component.find('.register-input').length).toEqual(5);
  expect(component.find('.username-input').props().value).toEqual('asdf');
  expect(component.find('.firstname-input').props().value).toEqual('asdf');
  expect(component.find('.lastname-input').props().value).toEqual('asdf');
  expect(component.find('.password-input').props().value).toEqual('asdf');
  expect(component.find('.confirm-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(1);
});

test('DOM renders correctly with all user data', () => {
  const component = shallow(
    <Register
      firstName={'asdf'}
      lastName={'asdf'}
      username={'asdf'}
      password={'asdf'}
      confirmPassword={'asdf'}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updatePassword={() => {}}
      updateConfirmPassword={() => {}}
      createUser={() => {}}
    />
  );

  expect(component.find('.register-input').length).toEqual(5);
  expect(component.find('.username-input').props().value).toEqual('asdf');
  expect(component.find('.firstname-input').props().value).toEqual('asdf');
  expect(component.find('.lastname-input').props().value).toEqual('asdf');
  expect(component.find('.password-input').props().value).toEqual('asdf');
  expect(component.find('.confirm-input').props().value).toEqual('asdf');
  expect(component.find('.submit-button').props().disabled).toBe(false);
  expect(component.find('.passwords-fail').length).toEqual(0);
});

test('DOM renders correctly with some user data', () => {
  const component = shallow(
    <Register
      firstName={'asdf'}
      lastName={'asdf'}
      username={'asdf'}
      password={'asdf'}
      confirmPassword={'asdfasf'}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updatePassword={() => {}}
      updateConfirmPassword={() => {}}
      createUser={() => {}}
    />
  );

  expect(component.find('.register-input').length).toEqual(5);
  expect(component.find('.username-input').props().value).toEqual('asdf');
  expect(component.find('.firstname-input').props().value).toEqual('asdf');
  expect(component.find('.lastname-input').props().value).toEqual('asdf');
  expect(component.find('.password-input').props().value).toEqual('asdf');
  expect(component.find('.confirm-input').props().value).toEqual('asdfasf');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(1);
});
