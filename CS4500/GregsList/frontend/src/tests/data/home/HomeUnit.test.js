'use es6';

import React from 'react';
import Home from '../../../components/home/Home';

import { shallow } from 'enzyme';
import { ServiceCategories, ThreeServiceCategories } from './HomeComponentData';

test('DOM renders correctly without service categories', () => {
  const component = shallow(
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

  expect(component.find('.service-category-button').length).toEqual(0);
  expect(component.find('.header-links').children().length).toEqual(2);
  expect(component.find('.search-bars').children().length).toEqual(3);
  expect(component.find('.nav-tabs').children().length).toEqual(0);
});

test('DOM contains the correct number of service categories and category tabs', () => {
  const component = shallow(
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

  expect(component.find('.service-category-button').length).toEqual(5);
  expect(component.find('.header-links').children().length).toEqual(2);
  expect(component.find('.search-bars').children().length).toEqual(3);
  expect(component.find('.nav-tabs').children().length).toEqual(5);
});

test("DOM contains the correct number of service categories and services when there're three categories", () => {
  const component = shallow(
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

  expect(component.find('.service-category-button').length).toEqual(3);
  expect(component.find('.header-links').children().length).toEqual(2);
  expect(component.find('.search-bars').children().length).toEqual(3);
  expect(component.find('.nav-tabs').children().length).toEqual(3);
});

test("DOM contains the correct number of services when there's a tab selected", () => {
  const component = shallow(
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

  expect(component.find('.row').children().length).toEqual(7);
});
