'use es6';

import React from 'react';
import ProfileEdit from '../../../components/profile/ProfileEdit';

import { shallow } from 'enzyme';

test('DOM renders correctly without user data', () => {
  const component = shallow(
    <ProfileEdit
      firstName={''}
      lastName={''}
      username={''}
      oldPasswordCheck={''}
      oldPassword={''}
      newPassword={''}
      confirmNewPassword={''}
      fetchLoggedInUserInfo={() => {}}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updateOldPassword={() => {}}
      updateNewPassword={() => {}}
      updateConfirmNewPassword={() => {}}
      updateUser={() => {}}
      nameError={false}
      oldPasswordError={false}
    />
  );

  expect(component.find('.profile-edit-input').length).toEqual(6);
  expect(component.find('.username-input').props().value).toEqual('');
  expect(component.find('.firstname-input').props().value).toEqual('');
  expect(component.find('.lastname-input').props().value).toEqual('');
  expect(
    component
      .find('.password-input')
      .at(0)
      .props().value
  ).toEqual('');
  expect(
    component
      .find('.password-input')
      .at(1)
      .props().value
  ).toEqual('');
  expect(component.find('.confirm-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(0);
  expect(component.find('.profile-edit-label-error').length).toEqual(0);
});

test('Old Password error renders when flag is set', () => {
  const component = shallow(
    <ProfileEdit
      firstName={''}
      lastName={''}
      username={''}
      oldPasswordCheck={''}
      oldPassword={''}
      newPassword={''}
      confirmNewPassword={''}
      fetchLoggedInUserInfo={() => {}}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updateOldPassword={() => {}}
      updateNewPassword={() => {}}
      updateConfirmNewPassword={() => {}}
      updateUser={() => {}}
      nameError={false}
      oldPasswordError={1}
    />
  );

  expect(component.find('.profile-edit-input').length).toEqual(6);
  expect(component.find('.username-input').props().value).toEqual('');
  expect(component.find('.firstname-input').props().value).toEqual('');
  expect(component.find('.lastname-input').props().value).toEqual('');
  expect(
    component
      .find('.password-input')
      .at(0)
      .props().value
  ).toEqual('');
  expect(
    component
      .find('.password-input')
      .at(1)
      .props().value
  ).toEqual('');
  expect(component.find('.confirm-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(0);
  expect(component.find('.profile-edit-label-error').length).toEqual(1);
});

test('Name error renders when flag is set', () => {
  const component = shallow(
    <ProfileEdit
      firstName={''}
      lastName={''}
      username={''}
      oldPasswordCheck={''}
      oldPassword={''}
      newPassword={''}
      confirmNewPassword={''}
      fetchLoggedInUserInfo={() => {}}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updateOldPassword={() => {}}
      updateNewPassword={() => {}}
      updateConfirmNewPassword={() => {}}
      updateUser={() => {}}
      nameError={false}
      oldPasswordError={1}
    />
  );

  expect(component.find('.profile-edit-input').length).toEqual(6);
  expect(component.find('.username-input').props().value).toEqual('');
  expect(component.find('.firstname-input').props().value).toEqual('');
  expect(component.find('.lastname-input').props().value).toEqual('');
  expect(
    component
      .find('.password-input')
      .at(0)
      .props().value
  ).toEqual('');
  expect(
    component
      .find('.password-input')
      .at(1)
      .props().value
  ).toEqual('');
  expect(component.find('.confirm-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(0);
  expect(component.find('.profile-edit-label-error').length).toEqual(1);
});

test('DOM renders correctly with no password fields filled', () => {
  const component = shallow(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsaws'}
      oldPasswordCheck={'ts1'}
      oldPassword={''}
      newPassword={''}
      confirmNewPassword={''}
      fetchLoggedInUserInfo={() => {}}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updateOldPassword={() => {}}
      updateNewPassword={() => {}}
      updateConfirmNewPassword={() => {}}
      updateUser={() => {}}
      nameError={false}
      oldPasswordError={false}
    />
  );

  expect(component.find('.profile-edit-input').length).toEqual(6);
  expect(component.find('.username-input').props().value).toEqual('tsaws');
  expect(component.find('.firstname-input').props().value).toEqual('tom');
  expect(component.find('.lastname-input').props().value).toEqual('sawyer');
  expect(
    component
      .find('.password-input')
      .at(0)
      .props().value
  ).toEqual('');
  expect(
    component
      .find('.password-input')
      .at(1)
      .props().value
  ).toEqual('');
  expect(component.find('.confirm-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(false);
  expect(component.find('.passwords-fail').length).toEqual(0);
  expect(component.find('.profile-edit-label-error').length).toEqual(0);
});

test('DOM renders correctly with only one password field filled', () => {
  const component = shallow(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsaws'}
      oldPasswordCheck={'ts1'}
      oldPassword={'ts1'}
      newPassword={'ts123'}
      confirmNewPassword={''}
      fetchLoggedInUserInfo={() => {}}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updateOldPassword={() => {}}
      updateNewPassword={() => {}}
      updateConfirmNewPassword={() => {}}
      updateUser={() => {}}
      nameError={false}
      oldPasswordError={false}
    />
  );

  expect(component.find('.profile-edit-input').length).toEqual(6);
  expect(component.find('.username-input').props().value).toEqual('tsaws');
  expect(component.find('.firstname-input').props().value).toEqual('tom');
  expect(component.find('.lastname-input').props().value).toEqual('sawyer');
  expect(
    component
      .find('.password-input')
      .at(0)
      .props().value
  ).toEqual('ts1');
  expect(
    component
      .find('.password-input')
      .at(1)
      .props().value
  ).toEqual('ts123');
  expect(component.find('.confirm-input').props().value).toEqual('');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(1);
  expect(component.find('.profile-edit-label-error').length).toEqual(0);
});

test('DOM renders correctly with all password fields filled', () => {
  const component = shallow(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsaws'}
      oldPasswordCheck={'ts1'}
      oldPassword={'ts1'}
      newPassword={'ts123'}
      confirmNewPassword={'ts123'}
      fetchLoggedInUserInfo={() => {}}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updateOldPassword={() => {}}
      updateNewPassword={() => {}}
      updateConfirmNewPassword={() => {}}
      updateUser={() => {}}
      nameError={false}
      oldPasswordError={false}
    />
  );

  expect(component.find('.profile-edit-input').length).toEqual(6);
  expect(component.find('.username-input').props().value).toEqual('tsaws');
  expect(component.find('.firstname-input').props().value).toEqual('tom');
  expect(component.find('.lastname-input').props().value).toEqual('sawyer');
  expect(
    component
      .find('.password-input')
      .at(0)
      .props().value
  ).toEqual('ts1');
  expect(
    component
      .find('.password-input')
      .at(1)
      .props().value
  ).toEqual('ts123');
  expect(component.find('.confirm-input').props().value).toEqual('ts123');
  expect(component.find('.submit-button').props().disabled).toBe(false);
  expect(component.find('.passwords-fail').length).toEqual(0);
  expect(component.find('.profile-edit-label-error').length).toEqual(0);
});

test('DOM renders correctly with all password fields filled, but confirm not matching', () => {
  const component = shallow(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsaws'}
      oldPasswordCheck={'ts1'}
      oldPassword={'ts1'}
      newPassword={'ts123'}
      confirmNewPassword={'ts1234'}
      fetchLoggedInUserInfo={() => {}}
      updateUsername={() => {}}
      updateFirstName={() => {}}
      updateLastName={() => {}}
      updateOldPassword={() => {}}
      updateNewPassword={() => {}}
      updateConfirmNewPassword={() => {}}
      updateUser={() => {}}
      nameError={false}
      oldPasswordError={false}
    />
  );

  expect(component.find('.profile-edit-input').length).toEqual(6);
  expect(component.find('.username-input').props().value).toEqual('tsaws');
  expect(component.find('.firstname-input').props().value).toEqual('tom');
  expect(component.find('.lastname-input').props().value).toEqual('sawyer');
  expect(
    component
      .find('.password-input')
      .at(0)
      .props().value
  ).toEqual('ts1');
  expect(
    component
      .find('.password-input')
      .at(1)
      .props().value
  ).toEqual('ts123');
  expect(component.find('.confirm-input').props().value).toEqual('ts1234');
  expect(component.find('.submit-button').props().disabled).toBe(true);
  expect(component.find('.passwords-fail').length).toEqual(1);
  expect(component.find('.profile-edit-label-error').length).toEqual(0);
});
