'use es6';

import React from 'react';
import { shallow } from 'enzyme';
import ServiceAnswerDetails from '../../../components/serviceAnswers/ServiceAnswerDetails';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

import { SERVICE_ANSWER_LIST } from './ServiceAnswerData';
import renderer from 'react-test-renderer';

configure({ adapter: new Adapter() });

test('Snapshot renders with data for selected answer', () => {
  let selectedServiceAnswer = SERVICE_ANSWER_LIST[2];

  const component = renderer.create(
    <ServiceAnswerDetails
      id={selectedServiceAnswer.id}
      serviceAnswers={SERVICE_ANSWER_LIST}
      serviceAnswer={selectedServiceAnswer}
      fetchServiceAnswer={jest.fn()}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot renders with null data for selected answer', () => {
  let selectedServiceAnswer = {
    id: null,
    trueFalseAnswer: null,
    minRangeAnswer: null,
    maxRangeAnswer: null,
    choiceAnswer: null,
  };

  const component = renderer.create(
    <ServiceAnswerDetails
      id={null}
      serviceAnswers={SERVICE_ANSWER_LIST}
      serviceAnswer={selectedServiceAnswer}
      fetchServiceAnswer={jest.fn()}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Initial DOM contains all fields with proper values for selected answer', () => {
  let selectedServiceAnswer = SERVICE_ANSWER_LIST[2];

  let component = shallow(
    <ServiceAnswerDetails
      id={selectedServiceAnswer.id}
      serviceAnswers={[]}
      serviceAnswer={selectedServiceAnswer}
      fetchServiceAnswer={jest.fn()}
    />
  );

  let selectedId = component.find('.service-q-a-details-id-select');
  let inputFields = component.find('.service-q-a-details-field-input');

  expect(selectedId.props().value).toEqual(3);
  expect(inputFields.length).toEqual(4);
  expect(inputFields.at(0).props().value).toEqual(true);
  expect(inputFields.at(1).props().value).toEqual(50);
  expect(inputFields.at(2).props().value).toEqual(100);
  expect(inputFields.at(3).props().value).toEqual(51);
});

test('Initial DOM contains all fields with null values for empty selected answer', () => {
  let selectedServiceAnswer = {
    id: null,
    trueFalseAnswer: null,
    minRangeAnswer: null,
    maxRangeAnswer: null,
    choiceAnswer: null,
  };

  let component = shallow(
    <ServiceAnswerDetails
      id={null}
      serviceAnswers={[]}
      serviceAnswer={selectedServiceAnswer}
      fetchServiceAnswer={jest.fn()}
    />
  );

  let selectedId = component.find('.service-q-a-details-id-select');
  let inputFields = component.find('.service-q-a-details-field-input');

  expect(selectedId.props().value).toEqual(null);
  expect(inputFields.length).toEqual(4);
  expect(inputFields.at(0).props().value).toEqual(null);
  expect(inputFields.at(1).props().value).toEqual(null);
  expect(inputFields.at(2).props().value).toEqual(null);
  expect(inputFields.at(3).props().value).toEqual(null);
});
