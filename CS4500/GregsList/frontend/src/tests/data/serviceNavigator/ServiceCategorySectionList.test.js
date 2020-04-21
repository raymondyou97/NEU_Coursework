import React from 'react';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';

import ServiceCategorySectionList from '../../../components/serviceNavigator/ServiceCategorySectionList';
import serviceCategories from './service-categories.mock.json';

test('Service Category Section List renders correct number of items', () => {
  const component = shallow(
    <ServiceCategorySectionList serviceCategories={serviceCategories} />
  );
  expect(component.find('li').length).toEqual(serviceCategories.length);

  const firstRow = component.find('li').first();
  expect(firstRow.key()).toEqual(serviceCategories[0].id);
});

test('Snapshot renders', () => {
  const component = renderer.create(
    <ServiceCategorySectionList serviceCategories={serviceCategories} />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
