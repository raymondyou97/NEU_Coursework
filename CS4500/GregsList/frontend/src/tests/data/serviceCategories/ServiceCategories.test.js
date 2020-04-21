'use es6';

import React from 'react';
import ServiceCategories from '../../../components/serviceCategories/ServiceCategories';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

import { SERVICE_CATEGORY_LIST } from './ServiceCategoryData';

configure({ adapter: new Adapter() });

test('Snapshot renders', () => {
  const serviceCategory = {
    title: '',
    description: '',
  };

  const component = renderer.create(
    <ServiceCategories
      fetchServiceCategories={() => {}}
      serviceCategory={serviceCategory}
      updateId={() => {}}
      serviceCategories={SERVICE_CATEGORY_LIST}
      updateTitle={() => {}}
      updateDescription={() => {}}
      createServiceCategory={() => {}}
      showDetails={() => {}}
      deleteServiceCategory={() => {}}
      updateServiceCategory={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Users component updates when there is user data', () => {
  const component = renderer.create(
    <ServiceCategories
      fetchServiceCategories={() => {}}
      serviceCategory={{
        title: 'Car Services',
        description: 'All things related to taking care of your car',
      }}
      updateId={() => {}}
      serviceCategories={SERVICE_CATEGORY_LIST}
      updateTitle={() => {}}
      updateDescription={() => {}}
      createServiceCategory={() => {}}
      showDetails={() => {}}
      deleteServiceCategory={() => {}}
      updateServiceCategory={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Initial DOM contains correct number of rows', () => {
  const serviceCategory = {
    title: '',
    description: '',
  };

  const component = shallow(
    <ServiceCategories
      fetchServiceCategories={() => {}}
      serviceCategory={serviceCategory}
      updateId={() => {}}
      serviceCategories={SERVICE_CATEGORY_LIST}
      updateTitle={() => {}}
      updateDescription={() => {}}
      createServiceCategory={() => {}}
      showDetails={() => {}}
      deleteServiceCategory={() => {}}
      updateServiceCategory={() => {}}
    />
  );

  expect(component.find('tr').length).toEqual(4);
});

test('Users component input value changes if selected user specified', () => {
  const serviceCategory = {
    title: 'Car Services',
    description: 'All things related to taking care of your car',
  };

  const component = shallow(
    <ServiceCategories
      fetchServiceCategories={() => {}}
      serviceCategory={serviceCategory}
      updateId={() => {}}
      serviceCategories={SERVICE_CATEGORY_LIST}
      updateTitle={() => {}}
      updateDescription={() => {}}
      createServiceCategory={() => {}}
      showDetails={() => {}}
      deleteServiceCategory={() => {}}
      updateServiceCategory={() => {}}
    />
  );

  expect(component.find('.service-category-title-input').props().value).toEqual(
    'Car Services'
  );
  expect(
    component.find('.service-category-description-input').props().value
  ).toEqual('All things related to taking care of your car');
});
