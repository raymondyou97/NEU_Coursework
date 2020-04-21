import React from 'react';
import { shallow } from 'enzyme';
import renderer from 'react-test-renderer';

import FAQDetailInfo from '../../../components/faqs/FAQDetailInfo';
import { makeFaqs } from './FaqData';

test('FAQ Detail Components', () => {
  const faqs = makeFaqs();

  const component = shallow(
    <FAQDetailInfo faq={faqs[0]} faqs={faqs} onChange={() => {}} />
  );
  expect(component.find('option').length).toEqual(faqs.length);

  const titleValue = component.find('input');
  expect(titleValue.at(0).props().value).toEqual(faqs[0].title);
  expect(titleValue.at(1).props().value).toEqual(faqs[0].question);
});

test('Snapshot renders', () => {
  const faqs = makeFaqs();

  const component = renderer.create(
    <FAQDetailInfo faq={faqs[0]} faqs={faqs} onChange={() => {}} />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
