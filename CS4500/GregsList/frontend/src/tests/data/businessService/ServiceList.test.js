import React from 'react';
import renderer from 'react-test-renderer';

import ServiceList from '../../../components/businessService/ServiceList';
import services from './business-service-questions.mock.json';

test('Snapshot renders', () => {
  const component = renderer.create(
    <ServiceList
      services={services}
      selectedService={undefined}
      setSelectedService={() => {}}
      setSelectedServices={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
