'use es6';

import React from 'react';
import Register from '../../../components/login/Register';
import renderer from 'react-test-renderer';

test('Empty snapshot renders', () => {
  const component = renderer.create(
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with user data renders', () => {
  const component = renderer.create(
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with user data renders', () => {
  const component = renderer.create(
    <Register
      firstName={'asdf'}
      lastName={'asdf'}
      username={'asdf'}
      password={'asdf'}
      confirmPassword={'asdf2'}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updatePassword={() => {}}
      updateConfirmPassword={() => {}}
      createUser={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with user data renders', () => {
  const component = renderer.create(
    <Register
      firstName={'asdf'}
      lastName={'asdf'}
      username={'asdf'}
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
