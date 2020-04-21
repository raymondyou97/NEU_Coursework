import React from 'react';
import { shallow } from 'enzyme';

import ServiceCategoryList from '../../../components/serviceNavigator/ServiceCategoryList';
import data from './service-categories.mock.json';

test('ServiceCategoryList', () => {
  const component = shallow(<ServiceCategoryList serviceCategories={data} />);
  expect(component.find('li').length).toEqual(data.length);

  // Check some assertions on the first element in the list
  const firstServiceCategory = data[0];
  const firstElement = component.find('li').first();
  const firstLink = firstElement.find('a');

  expect(firstLink).toBeDefined();
  expect(firstLink.props().href).toEqual(`#${firstServiceCategory.id}`);
  expect(firstLink.text()).toEqual(firstServiceCategory.title);
});
