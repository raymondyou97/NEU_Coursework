import React from 'react';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import ServiceCards from '../../../components/serviceNavigator/ServiceCards';
import serviceCategories from './service-categories.mock.json';

test('Service Cards renders correct number of items', () => {
  const component = shallow(
    <ServiceCards services={serviceCategories[0].services} />
  );

  expect(component.find('Card').length).toEqual(
    serviceCategories[0].services.length
  );
});

test('Service Cards renders correct cards', () => {
  const component = shallow(
    <ServiceCards services={serviceCategories[0].services} />
  );

  expect(
    component
      .find('Card')
      .first()
      .key()
  ).toEqual(serviceCategories[0].services[0].id);
});

test('Snapshot renders: ServiceCards', () => {
  const component = renderer.create(
    <ServiceCards services={serviceCategories[0].services} />
  );
  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
