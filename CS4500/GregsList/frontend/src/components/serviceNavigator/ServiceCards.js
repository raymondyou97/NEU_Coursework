import React from 'react';

import { Card, CardDeck } from 'react-bootstrap';

const ServiceCards = ({ services }) => (
  <CardDeck>
    {services.map(service => (
      <Card
        key={service.id}
        style={{
          flex: 'none',
          flexDirection: 'column',
          flexWrap: 'wrap',
          marginBottom: '15px',
          maxHeight: '100%',
          maxWidth: '50%',
        }}
      >
        <Card.Img variant="top" src="https://picsum.photos/300/200" />
        <Card.Body>
          <Card.Text>
            <a href={'/ServiceProviderSearch/' + service.id}>
              {' '}
              {service.title}
            </a>
          </Card.Text>
        </Card.Body>
      </Card>
    ))}
  </CardDeck>
);

export default ServiceCards;
