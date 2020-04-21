import React from 'react';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';

import FAQAnswerRows from '../../../components/faas/FAQAnswerRows';
import { findAllFAQAnswers } from './MockFaaService';

test('FAQ Answer Rows', () => {
  const faas = findAllFAQAnswers();

  const component = shallow(<FAQAnswerRows faas={faas} />);
  expect(component.find('tr').length).toEqual(faas.length);

  const firstRow = component.find('tr').first();
  expect(
    firstRow
      .find('td')
      .at(0)
      .text()
  ).toEqual(faas[0].question);
  expect(
    firstRow
      .find('td')
      .at(1)
      .text()
  ).toEqual(faas[0].answer);
});

test('Snapshot renders', () => {
  const faas = findAllFAQAnswers();

  const component = renderer.create(<FAQAnswerRows faas={faas} />);

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
