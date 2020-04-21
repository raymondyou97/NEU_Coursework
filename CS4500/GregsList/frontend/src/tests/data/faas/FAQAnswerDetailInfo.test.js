import React from 'react';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';

import FAQAnswerDetailInfo from '../../../components/faas/FAQAnswerDetailInfo';
import { findAllFAQAnswers } from './MockFaaService';

test('FAQ Answer Detail Components', () => {
  const faas = findAllFAQAnswers();

  const component = shallow(
    <FAQAnswerDetailInfo
      faqAnswer={faas[0]}
      faqAnswers={faas}
      onChange={() => {}}
    />
  );
  expect(component.find('option').length).toEqual(faas.length);

  const titleValue = component.find('input');
  expect(titleValue.at(0).props().value).toEqual(faas[0].question);
  expect(titleValue.at(1).props().value).toEqual(faas[0].answer);
});

test('Snapshot renders', () => {
  const faas = findAllFAQAnswers();

  const component = renderer.create(
    <FAQAnswerDetailInfo
      faqAnswer={faas[0]}
      faqAnswers={faas}
      onChange={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
