'use es6';

import { SERVICE_LIST } from './ServiceData';

export const mockDeleteService = id => {
  return { status: 200 };
};

export const mockFindServiceById = id => {
  SERVICE_LIST.forEach(service => {
    if (service.id === id) {
      return service;
    }
  });
  return [];
};

export const mockFindAllServices = () => {
  return SERVICE_LIST;
};

export const mockCreateService = data => {
  return data;
};

export const mockUpdateService = (id, data) => {
  SERVICE_LIST.forEach(service => {
    if (service.id === id) {
      let newData = Object.assign(service, data);
      return newData;
    }
  });
  return data;
};
