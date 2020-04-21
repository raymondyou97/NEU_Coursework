import React from 'react';
import renderer from 'react-test-renderer';

import SelectedServicesList from '../../../components/businessService/SelectedServicesList';
import data from './selected-services.mock.json';

test('SelectedServicesList Snapshot renders', () => {
  const component = renderer.create(
    <SelectedServicesList
      selectedServices={data}
      selectedSelectedServices={() => {}}
      selectedSelectedService={data[0]['id']}
      setSelectedSelectedService={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
