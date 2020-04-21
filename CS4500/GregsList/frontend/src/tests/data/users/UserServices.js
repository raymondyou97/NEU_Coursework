'use es6';

import { USER_LIST } from './UserData';

export const mockDeleteService = id => {
  return {
    status: 200,
  };
};

export const mockFindAllUsers = () => {
  return USER_LIST;
};

export const mockCreateUser = () => {
  return {
    id: 123,
    username: 'mock-user-name',
    firstName: 'mock-first-name',
    lastName: 'mock-last-name',
  };
};

export const mockFindUserById = userId => {
  return {
    id: userId,
    username: 'mock-user-name',
    firstName: 'mock-first-name',
    lastName: 'mock-last-name',
  };
};

export const mockUpdateUser = (id, data) => {
  return {
    id,
    ...data,
  };
};
