import React, { useEffect, useMemo, useState } from 'react';
import ServiceCategoryList from './ServiceCategoryList';
import ServiceCategorySectionList from './ServiceCategorySectionList';
import ServiceProviderSearch from '../serviceProviderSearch/ServiceProviderSearch';
import ServiceCategoryService from '../../services/ServiceCategoryService';

import { Container } from 'react-bootstrap';

const ServiceNavigator = () => {
  // Memoized instance of the service
  const serviceCategoryService = useMemo(
    () => ServiceCategoryService.getInstance(),
    []
  );
  const [categories, setCategories] = useState(undefined);

  // On-mount function to load data from the API
  useEffect(() => {
    serviceCategoryService.findAllServiceCategories().then(setCategories);
  }, []);

  return (
    <Container>
      <div className="row">
        <div className="col-8">
          <ServiceProviderSearch />
        </div>
        <div className="col-3 text-right">
          <a href="SignUp">Sign up</a>
        </div>
        <div className="col-1">
          <a href="LogIn">Log in</a>
        </div>
      </div>
      <br />
      <br />
      {categories && (
        <div className="row">
          <div className="col-3">
            <ServiceCategoryList serviceCategories={categories} />
          </div>
          <div className="col-9">
            <ServiceCategorySectionList serviceCategories={categories} />
          </div>
        </div>
      )}
    </Container>
  );
};

export default ServiceNavigator;
