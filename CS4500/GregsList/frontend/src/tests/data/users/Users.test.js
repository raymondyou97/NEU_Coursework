'use es6';

import React from 'react';
import Users from '../../../components/users/Users';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';

import { USER_LIST } from './UserData';

test('Snapshot renders', () => {
  const selectedUser = {
    username: '',
    firstName: '',
    lastName: '',
  };

  const component = renderer.create(
    <Users
      fetchUsers={() => {}}
      selectedUser={selectedUser}
      selectUser={() => {}}
      users={USER_LIST}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      createUser={() => {}}
      showDetails={() => {}}
      deleteUser={() => {}}
      updateUser={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Users component updates when there is user data', () => {
  const component = renderer.create(
    <Users
      fetchUsers={() => {}}
      selectedUser={{
        username: 'spoonily',
        firstName: 'Jonah',
        lastName: 'Min',
      }}
      selectUser={() => {}}
      users={USER_LIST}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      createUser={() => {}}
      showDetails={() => {}}
      deleteUser={() => {}}
      updateUser={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Initial DOM contains correct number of rows', () => {
  const selectedUser = {
    username: '',
    firstName: '',
    lastName: '',
  };

  const component = shallow(
    <Users
      fetchUsers={() => {}}
      selectedUser={selectedUser}
      selectUser={() => {}}
      users={USER_LIST}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      createUser={() => {}}
      showDetails={() => {}}
      deleteUser={() => {}}
      updateUser={() => {}}
    />
  );

  expect(component.find('tr').length).toEqual(5);
});

test('Users component input value changes if selected user specified', () => {
  const selectedUser = {
    username: 'spoonily',
    firstName: 'Jonah',
    lastName: 'Min',
  };

  const component = shallow(
    <Users
      fetchUsers={() => {}}
      selectedUser={selectedUser}
      selectUser={() => {}}
      users={USER_LIST}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      createUser={() => {}}
      showDetails={() => {}}
      deleteUser={() => {}}
      updateUser={() => {}}
    />
  );

  expect(component.find('.user-input-username').props().value).toEqual(
    'spoonily'
  );
  expect(component.find('.user-input-firstname').props().value).toEqual(
    'Jonah'
  );
  expect(component.find('.user-input-lastname').props().value).toEqual('Min');
});
