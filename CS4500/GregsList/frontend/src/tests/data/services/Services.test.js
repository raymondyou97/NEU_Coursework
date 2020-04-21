'use es6';

import React from 'react';
import Services from '../../../components/services/Services';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

import { SERVICE_LIST } from './ServiceData';

configure({ adapter: new Adapter() });

test('Snapshot renders', () => {
  const component = renderer.create(
    <Services
      newTitle={''}
      findAllServices={() => {}}
      enableEdits={() => {}}
      services={SERVICE_LIST}
      handleTitleChange={() => {}}
      createService={() => {}}
      showService={() => {}}
      deleteService={() => {}}
      updateService={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Services component updates when there is service data', () => {
  const component = renderer.create(
    <Services
      newTitle={''}
      findAllServices={() => {}}
      enableEdits={() => {}}
      services={SERVICE_LIST}
      handleTitleChange={() => {}}
      createService={() => {}}
      showService={() => {}}
      deleteService={() => {}}
      updateService={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Initial DOM contains correct number of rows', () => {
  const component = shallow(
    <Services
      newTitle={''}
      findAllServices={() => {}}
      enableEdits={() => {}}
      services={SERVICE_LIST}
      handleTitleChange={() => {}}
      createService={() => {}}
      showService={() => {}}
      deleteService={() => {}}
      updateService={() => {}}
    />
  );

  expect(component.find('tr').length).toEqual(5);
});

test('Services component input value changes if selected title', () => {
  const component = shallow(
    <Services
      newTitle={'Dog Walking'}
      findAllServices={() => {}}
      enableEdits={() => {}}
      services={SERVICE_LIST}
      handleTitleChange={() => {}}
      createService={() => {}}
      showService={() => {}}
      deleteService={() => {}}
      updateService={() => {}}
    />
  );

  expect(component.find('.service-input-title').props().value).toEqual(
    'Dog Walking'
  );
});
