'use es6';

import React from 'react';
import BusinessAddress from '../../../components/business/Address';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

configure({ adapter: new Adapter() });

test('Initial snapshot renders', () => {
  const component = renderer.create(<BusinessAddress />);

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Correct number of default forms and default values', () => {
  const component = shallow(<BusinessAddress />);

  expect(component.find('.form-control').length).toEqual(4);
  expect(component.find('#businessStreetInput').props().value).toEqual(
    undefined
  );
  expect(component.find('#businessCityInput').props().value).toEqual(undefined);
  expect(component.find('#businessZipInput').props().value).toEqual(undefined);
});
