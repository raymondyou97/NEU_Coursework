'use es6';

import React from 'react';
import BusinessGeneral from '../../../components/business/General';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

configure({ adapter: new Adapter() });

test('Initial snapshot renders', () => {
  const component = renderer.create(<BusinessGeneral />);

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Correct number of default forms and default values', () => {
  const component = shallow(<BusinessGeneral />);

  expect(component.find('.form-control').length).toEqual(4);
  expect(component.find('#businessNameInput').props().value).toEqual(undefined);
  expect(component.find('#businessYearFoundedInput').props().value).toEqual(
    undefined
  );
  expect(component.find('#businessNumEmployeesInput').props().value).toEqual(
    undefined
  );
  expect(component.find('#businessEmailInput').props().value).toEqual(
    undefined
  );
});
