'use es6';

import React from 'react';
import Login from '../../../components/login/Login';
import renderer from 'react-test-renderer';

test('Empty snapshot renders', () => {
  const component = renderer.create(
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Login with user data renders', () => {
  const component = renderer.create(
    <Login
      validateUser={() => {}}
      updateUsername={() => {}}
      updatePassword={() => {}}
      setError={() => {}}
      username={'jonah'}
      password={'password'}
      error={false}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with data and error renders', () => {
  const component = renderer.create(
    <Login
      validateUser={() => {}}
      updateUsername={() => {}}
      updatePassword={() => {}}
      setError={() => {}}
      username={'asdf'}
      password={'password'}
      error={true}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
