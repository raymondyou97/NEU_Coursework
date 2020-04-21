'use es6';

import jest from 'jest';
import { SERVICE_CATEGORY_LIST } from './ServiceCategoryData';

global.fetch = jest.fn().mockImplementation((url, config) => {
  if (!config || config.method === 'GET') {
    if (url.indexOf('/api/categories/0') !== -1) {
      return new Promise((resolve, reject) => {
        resolve({
          json: function() {
            return SERVICE_CATEGORY_LIST[0];
          },
        });
      });
    } else if (url.indexOf('api/categories') !== -1) {
      return new Promise((resolve, reject) => {
        resolve({
          json: function() {
            return SERVICE_CATEGORY_LIST[0];
          },
        });
      });
    }
  } else if (config.method === 'POST') {
    if (url.indexOf('/api/categories') !== -1) {
      return new Promise((resolve, reject) => {
        resolve({
          json: function() {
            return '';
          },
        });
      });
    }
  } else if (config.method === 'PUT') {
    if (url.indexOf('/api/categories/0') !== -1) {
      return new Promise((resolve, reject) => {
        resolve({
          json: function() {
            return '';
          },
        });
      });
    }
  } else if (config.method === 'DELETE') {
    if (url.indexOf('/api/categories/0') !== -1) {
      return new Promise((resolve, reject) => {
        resolve({
          json: function() {
            return '';
          },
        });
      });
    }
  }
});
