'use es6';

import React from 'react';
import BusinessIndex from '../../../components/business/';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

configure({ adapter: new Adapter() });

test('Initial snapshot renders', () => {
  const component = renderer.create(<BusinessIndex />);

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
