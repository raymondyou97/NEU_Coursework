import React from 'react';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';

import FAQRows from '../../../components/faqs/FAQRows';
import { makeFaqs } from './FaqData';

test('FAQRows', () => {
  const faqs = makeFaqs();

  const component = shallow(<FAQRows faqs={faqs} />);
  expect(component.find('tr').length).toEqual(faqs.length);

  const firstRow = component.find('tr').first();
  expect(
    firstRow
      .find('td')
      .at(0)
      .text()
  ).toEqual(faqs[0].title);
  expect(
    firstRow
      .find('td')
      .at(1)
      .text()
  ).toEqual(faqs[0].question);
});

test('Snapshot renders', () => {
  const faqs = makeFaqs();

  const component = renderer.create(<FAQRows faqs={faqs} />);

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
