'use es6';

import React from 'react';
import ServiceQuestions from '../../../components/serviceQuestions/ServiceQuestions';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';
import { configure } from 'enzyme';
import Adapter from 'enzyme-adapter-react-16';

import { SERVICE_QUESTION_LIST } from './ServiceQuestionData';

configure({ adapter: new Adapter() });

test('Snapshot renders', () => {
  let selectedServiceQuestion = {
    newQuestion: '',
    newType: '',
    newChoices: '',
  };

  const component = renderer.create(
    <ServiceQuestions
      serviceQuestions={SERVICE_QUESTION_LIST}
      selectedServiceQuestion={selectedServiceQuestion}
      serviceQuestionIDChoices={[]}
      fetchServiceQuestions={() => {}}
      handleQuestionChange={() => {}}
      handleTypeChange={() => {}}
      handleChoicesChange={() => {}}
      handleCountChange={() => {}}
      createServiceQuestion={() => {}}
      showServiceQuestionDetails={() => {}}
      deleteServiceQuestion={() => {}}
      updateServiceQuestion={() => {}}
      getServiceQuestionIDs={() => {}}
      pageLeft={() => {}}
      pageRight={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot renders service questions component updates when there is data entered into the input boxes', () => {
  let selectedServiceQuestion = {
    newQuestion: 'what is love?',
    newType: 'what is life?',
    newChoices: 'what is death?',
  };

  const component = renderer.create(
    <ServiceQuestions
      serviceQuestions={SERVICE_QUESTION_LIST}
      selectedServiceQuestion={selectedServiceQuestion}
      serviceQuestionIDChoices={[]}
      fetchServiceQuestions={() => {}}
      handleQuestionChange={() => {}}
      handleTypeChange={() => {}}
      handleChoicesChange={() => {}}
      handleCountChange={() => {}}
      createServiceQuestion={() => {}}
      showServiceQuestionDetails={() => {}}
      deleteServiceQuestion={() => {}}
      updateServiceQuestion={() => {}}
      getServiceQuestionIDs={() => {}}
      pageLeft={() => {}}
      pageRight={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Initial DOM contains correct number of rows of service questions including input row', () => {
  let selectedServiceQuestion = {
    newQuestion: '',
    newType: '',
    newChoices: '',
  };

  let component = shallow(
    <ServiceQuestions
      serviceQuestions={[]}
      selectedServiceQuestion={selectedServiceQuestion}
      serviceQuestionIDChoices={[]}
      fetchServiceQuestions={() => {}}
      handleQuestionChange={() => {}}
      handleTypeChange={() => {}}
      handleChoicesChange={() => {}}
      handleCountChange={() => {}}
      createServiceQuestion={() => {}}
      showServiceQuestionDetails={() => {}}
      deleteServiceQuestion={() => {}}
      updateServiceQuestion={() => {}}
      getServiceQuestionIDs={() => {}}
      pageLeft={() => {}}
      pageRight={() => {}}
    />
  );

  expect(
    component.find('.service-question-table .service-q-a-table-row').length
  ).toEqual(1);

  component = shallow(
    <ServiceQuestions
      serviceQuestions={SERVICE_QUESTION_LIST}
      selectedServiceQuestion={selectedServiceQuestion}
      serviceQuestionIDChoices={[]}
      fetchServiceQuestions={() => {}}
      handleQuestionChange={() => {}}
      handleTypeChange={() => {}}
      handleChoicesChange={() => {}}
      handleCountChange={() => {}}
      createServiceQuestion={() => {}}
      showServiceQuestionDetails={() => {}}
      deleteServiceQuestion={() => {}}
      updateServiceQuestion={() => {}}
      getServiceQuestionIDs={() => {}}
      pageLeft={() => {}}
      pageRight={() => {}}
    />
  );

  expect(
    component.find('.service-question-table .service-q-a-table-row').length
  ).toEqual(4);
});

test('Service question component input value changes if input is entered', () => {
  let selectedServiceQuestion = {
    newQuestion: '',
    newType: '',
    newChoices: '',
  };

  let component = shallow(
    <ServiceQuestions
      serviceQuestions={SERVICE_QUESTION_LIST}
      selectedServiceQuestion={selectedServiceQuestion}
      serviceQuestionIDChoices={[]}
      fetchServiceQuestions={() => {}}
      handleQuestionChange={() => {}}
      handleTypeChange={() => {}}
      handleChoicesChange={() => {}}
      handleCountChange={() => {}}
      createServiceQuestion={() => {}}
      showServiceQuestionDetails={() => {}}
      deleteServiceQuestion={() => {}}
      updateServiceQuestion={() => {}}
      getServiceQuestionIDs={() => {}}
      pageLeft={() => {}}
      pageRight={() => {}}
    />
  );

  expect(
    component.find('.service-question-input-question').props().value
  ).toEqual('');
  expect(component.find('.service-question-input-type').props().value).toEqual(
    ''
  );
  expect(
    component.find('.service-question-input-choices').props().value
  ).toEqual('');

  selectedServiceQuestion = {
    newQuestion: 'what is love?',
    newType: 'what is life?',
    newChoices: 'what is death?',
  };

  component = shallow(
    <ServiceQuestions
      serviceQuestions={SERVICE_QUESTION_LIST}
      selectedServiceQuestion={selectedServiceQuestion}
      serviceQuestionIDChoices={[]}
      fetchServiceQuestions={() => {}}
      handleQuestionChange={() => {}}
      handleTypeChange={() => {}}
      handleChoicesChange={() => {}}
      handleCountChange={() => {}}
      createServiceQuestion={() => {}}
      showServiceQuestionDetails={() => {}}
      deleteServiceQuestion={() => {}}
      updateServiceQuestion={() => {}}
      getServiceQuestionIDs={() => {}}
      pageLeft={() => {}}
      pageRight={() => {}}
    />
  );

  expect(
    component.find('.service-question-input-question').props().value
  ).toEqual('what is love?');
  expect(component.find('.service-question-input-type').props().value).toEqual(
    'what is life?'
  );
  expect(
    component.find('.service-question-input-choices').props().value
  ).toEqual('what is death?');
});
