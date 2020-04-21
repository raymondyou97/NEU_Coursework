import React from 'react';
import ServiceCards from './ServiceCards';

const ServiceCategorySection = ({ serviceCategory }) => (
  <div>
    <h2 id={serviceCategory.id}>{serviceCategory.title}</h2>
    <div>
      <div>
        <ServiceCards services={serviceCategory.services.slice(0, 4)} />
        {serviceCategory.services.map(service => (
          <div key={service.id}>
            <a href="/providers"> {service.title}</a>
          </div>
        ))}
      </div>
    </div>
  </div>
);

export default ServiceCategorySection;
