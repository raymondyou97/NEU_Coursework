'use es6';

import React from 'react';
import Home from '../../../components/home/Home';
import renderer from 'react-test-renderer';
import { ServiceCategories, ThreeServiceCategories } from './HomeComponentData';

test('Empty snapshot renders', () => {
  const component = renderer.create(
    <Home
      fetchServiceCategories={() => {}}
      fetchTabServiceCategories={() => {}}
      fetchLoggedInUser={() => {}}
      serviceCategories={[]}
      tabServiceCategories={[]}
      selectServiceTabs={() => {}}
      selectedTab={-1}
      loggedInUser={null}
      logOut={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with data renders', () => {
  const component = renderer.create(
    <Home
      fetchServiceCategories={() => {}}
      fetchTabServiceCategories={() => {}}
      fetchLoggedInUser={() => {}}
      serviceCategories={ServiceCategories}
      tabServiceCategories={ServiceCategories}
      selectServiceTabs={() => {}}
      selectedTab={-1}
      loggedInUser={null}
      logOut={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with less data renders', () => {
  const component = renderer.create(
    <Home
      fetchServiceCategories={() => {}}
      fetchTabServiceCategories={() => {}}
      fetchLoggedInUser={() => {}}
      serviceCategories={ThreeServiceCategories}
      tabServiceCategories={ThreeServiceCategories}
      selectServiceTabs={() => {}}
      selectedTab={-1}
      loggedInUser={null}
      logOut={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});

test('Snapshot with tab selected renders', () => {
  const component = renderer.create(
    <Home
      fetchServiceCategories={() => {}}
      fetchTabServiceCategories={() => {}}
      fetchLoggedInUser={() => {}}
      serviceCategories={ServiceCategories}
      tabServiceCategories={ServiceCategories}
      selectServiceTabs={() => {}}
      selectedTab={0}
      loggedInUser={null}
      logOut={() => {}}
    />
  );

  let componentTree = component.toJSON();
  expect(componentTree).toMatchSnapshot();
});
