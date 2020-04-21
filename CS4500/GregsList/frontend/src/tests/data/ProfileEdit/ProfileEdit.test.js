'use es6';

import React from 'react';
import renderer from 'react-test-renderer';
import ProfileEdit from '../../../components/profile/ProfileEdit';

test('Empty snapshot renders', () => {
  const component = renderer.create(
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with all user data renders', () => {
  const component = renderer.create(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsawyer'}
      oldPasswordCheck={'ts'}
      oldPassword={'ts'}
      newPassword={'tsaw'}
      confirmNewPassword={'tsaw'}
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with user data but non-matching new passwords renders', () => {
  const component = renderer.create(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsawyer'}
      oldPasswordCheck={'ts'}
      oldPassword={'ts'}
      newPassword={'tsaw'}
      confirmNewPassword={'tsaw123'}
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with user data and no passwords renders', () => {
  const component = renderer.create(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsawyer'}
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with user data and only half of password fields filled renders', () => {
  const component = renderer.create(
    <ProfileEdit
      firstName={'tom'}
      lastName={'sawyer'}
      username={'tsawyer'}
      oldPasswordCheck={'ts'}
      oldPassword={'ts'}
      newPassword={'sawy'}
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

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
