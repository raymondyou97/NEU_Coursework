import React from 'react';
import PropTypes from 'prop-types';

import { ListGroup } from 'react-bootstrap';

const ServiceList = ({
  services,
  selectedService,
  setSelectedService,
  setSelectedServices,
}) => {
  if (services) {
    return (
      <ListGroup>
        {services.map(({ id, title }) => {
          const isSelected = selectedService === id;
          return (
            <ListGroup.Item
              key={id}
              active={isSelected}
              onClick={() => {
                setSelectedService(id === selectedService ? undefined : id);
                setSelectedServices(prevServices => {
                  if (prevServices.findIndex(ss => ss.id === id) === -1) {
                    return [...prevServices, { id, title }];
                  } else {
                    return prevServices;
                  }
                });
              }}
            >
              {title} ✓
            </ListGroup.Item>
          );
        })}
      </ListGroup>
    );
  }

  return null;
};

ServiceList.propTypes = {
  services: PropTypes.arrayOf(PropTypes.object.isRequired),
  selectedService: PropTypes.number,
  setSelectedService: PropTypes.func.isRequired,
  setSelectedServices: PropTypes.func.isRequired,
};

export default ServiceList;
