'use es6';

import React from 'react';
import { shallow } from 'enzyme';
import ServiceAnswers from '../../../components/serviceAnswers/ServiceAnswers';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

import { SERVICE_ANSWER_LIST } from './ServiceAnswerData';

configure({ adapter: new Adapter() });

test('Snapshot renders', () => {
  let selectedServiceAnswer = {
    trueFalseAnswer: '',
    minRangeAnswer: '',
    maxRangeAnswer: '',
    choiceAnswer: '',
  };

  const component = renderer.create(
    <ServiceAnswers
      serviceAnswers={SERVICE_ANSWER_LIST}
      selectedServiceAnswer={selectedServiceAnswer}
      fetchServiceAnswers={jest.fn()}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot renders when there is date entered into the input boxes', () => {
  let selectedServiceAnswer = {
    trueFalseAnswer: false,
    minRangeAnswer: 1,
    maxRangeAnswer: 3,
    choiceAnswer: 2,
  };

  const component = renderer.create(
    <ServiceAnswers
      serviceAnswers={SERVICE_ANSWER_LIST}
      selectedServiceAnswer={selectedServiceAnswer}
      fetchServiceAnswers={jest.fn()}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test(
  'Initial DOM contains correct number of rows of service answers' +
    ' including input row',
  () => {
    let selectedServiceAnswer = {
      trueFalseAnswer: '',
      minRangeAnswer: '',
      maxRangeAnswer: '',
      choiceAnswer: '',
    };

    let component = shallow(
      <ServiceAnswers
        serviceAnswers={[]}
        selectedServiceAnswer={selectedServiceAnswer}
        fetchServiceAnswers={jest.fn()}
      />
    );

    expect(
      component.find('.service-answer-table .service-q-a-table-row').length
    ).toEqual(1);

    component = shallow(
      <ServiceAnswers
        serviceAnswers={SERVICE_ANSWER_LIST}
        selectedServiceAnswer={selectedServiceAnswer}
        fetchServiceAnswers={jest.fn()}
      />
    );

    expect(
      component.find('.service-answer-table .service-q-a-table-row').length
    ).toEqual(4);
  }
);

test('Service answer component input value changes if input is entered', () => {
  let selectedServiceAnswer = {
    trueFalseAnswer: false,
    minRangeAnswer: 1,
    maxRangeAnswer: 3,
    choiceAnswer: 2,
  };

  let component = shallow(
    <ServiceAnswers
      serviceAnswers={SERVICE_ANSWER_LIST}
      selectedServiceAnswer={selectedServiceAnswer}
      fetchServiceAnswers={jest.fn()}
    />
  );

  expect(
    component.find('.service-answer-input-true-false').props().value
  ).toEqual(false);
  expect(
    component.find('.service-answer-input-min-range').props().value
  ).toEqual(1);
  expect(
    component.find('.service-answer-input-max-range').props().value
  ).toEqual(3);
  expect(component.find('.service-answer-input-choice').props().value).toEqual(
    2
  );

  selectedServiceAnswer = {
    trueFalseAnswer: true,
    minRangeAnswer: null,
    maxRangeAnswer: null,
    choiceAnswer: null,
  };

  component = shallow(
    <ServiceAnswers
      serviceAnswers={SERVICE_ANSWER_LIST}
      selectedServiceAnswer={selectedServiceAnswer}
      fetchServiceAnswers={jest.fn()}
    />
  );

  expect(
    component.find('.service-answer-input-true-false').props().value
  ).toEqual(true);
  expect(
    component.find('.service-answer-input-min-range').props().value
  ).toEqual(null);
  expect(
    component.find('.service-answer-input-max-range').props().value
  ).toEqual(null);
  expect(component.find('.service-answer-input-choice').props().value).toEqual(
    null
  );
});
