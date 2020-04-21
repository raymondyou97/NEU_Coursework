import React from 'react';
import ServiceCategorySection from './ServiceCategorySection';

const ServiceCategorySectionList = ({ serviceCategories }) => (
  <ul>
    {serviceCategories.map(serviceCategory => (
      <li key={serviceCategory.id} style={{ listStyle: 'none' }}>
        <div>
          <ServiceCategorySection serviceCategory={serviceCategory} />
        </div>
      </li>
    ))}
  </ul>
);

export default ServiceCategorySectionList;
