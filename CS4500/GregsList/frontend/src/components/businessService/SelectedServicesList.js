import React from 'react';
import PropTypes from 'prop-types';

import { ListGroup } from 'react-bootstrap';

const SelectedServicesList = ({
  selectedServices,
  setSelectedServices,
  selectedSelectedService,
  setSelectedSelectedService,
}) => {
  if (selectedServices) {
    return (
      <ListGroup>
        {selectedServices.map(({ id, title }) => {
          const isSelected = selectedSelectedService === id;
          return (
            <ListGroup.Item
              key={id}
              active={isSelected}
              onClick={() =>
                setSelectedSelectedService(
                  id === selectedSelectedService ? undefined : id
                )
              }
            >
              {title}
              <button
                onClick={() => {
                  setSelectedServices(
                    selectedServices.filter(x => x.id !== id)
                  );
                  setSelectedSelectedService(
                    isSelected ? undefined : selectedSelectedService
                  );
                }}
              >
                {'X'}
              </button>
            </ListGroup.Item>
          );
        })}
      </ListGroup>
    );
  }

  return null;
};

SelectedServicesList.propTypes = {
  selectedServices: PropTypes.arrayOf(PropTypes.object.isRequired),
  selectedSelectedService: PropTypes.number,
  setSelectedSelectedService: PropTypes.func.isRequired,
};

export default SelectedServicesList;
