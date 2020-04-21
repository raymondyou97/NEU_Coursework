'use es6';

import React from 'react';
import ServiceProviderFilter from '../../../../components/serviceProviderSearch/ServiceProviderFilter';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

import { SERVICE_QUESTION_LIST } from './ServiceProviderFilterData';

configure({ adapter: new Adapter() });

test('Snapshot renders with no service questions', () => {
  let serviceQuestions = [];
  const component = renderer.create(
    <ServiceProviderFilter serviceQuestions={serviceQuestions} />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot renders with service questions', () => {
  const component = renderer.create(
    <ServiceProviderFilter serviceQuestions={SERVICE_QUESTION_LIST} />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('there exists 3 service questions', () => {
  let component = shallow(
    <ServiceProviderFilter serviceQuestions={SERVICE_QUESTION_LIST} />
  );

  expect(component.find('.service-filter-question').length).toEqual(3);
});

test('there exists 4 choices for the one multiple choice question', () => {
  let component = shallow(
    <ServiceProviderFilter serviceQuestions={SERVICE_QUESTION_LIST} />
  );

  expect(component.find('.multiple-choice-option').length).toEqual(4);
});

test('there exists 2 choices for the one true/false question', () => {
  let component = shallow(
    <ServiceProviderFilter serviceQuestions={SERVICE_QUESTION_LIST} />
  );

  expect(component.find('.true-false-option').length).toEqual(2);
});

test('there exists 1 range question', () => {
  let component = shallow(
    <ServiceProviderFilter serviceQuestions={SERVICE_QUESTION_LIST} />
  );

  expect(component.find('.range-question').length).toEqual(1);
});
