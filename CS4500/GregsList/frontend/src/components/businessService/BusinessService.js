import React, { useEffect, useMemo, useState } from 'react';
import { Container } from 'react-bootstrap';

import ServiceList from './ServiceList';
import SelectedServicesList from './SelectedServicesList';
import ServiceQuestion from './ServiceQuestion';
import ServiceService from '../../services/ServiceService';
import UserService from '../../services/UserService';

const BusinessService = () => {
  // Memoized instance of the service
  const serviceService = useMemo(() => ServiceService.getInstance(), []);
  const userService = useMemo(() => UserService.getInstance(), []);
  const [services, setServices] = useState(undefined);
  const [serviceSearch, setServiceSearch] = useState('');
  const [selectedService, setSelectedService] = useState(undefined);
  const [selectedServices, setSelectedServices] = useState([]);
  const [selectedSelectedService, setSelectedSelectedService] = useState(
    undefined
  );
  const [user, setUser] = useState(undefined);

  // On-mount function to load data from the API
  useEffect(() => {
    serviceService.findAllServices().then(setServices);
    const userId = localStorage.getItem('loggedInUser');
    userService.findUserByUsername(userId).then(setUser);
  }, []);

  // Filter services by the search term
  const filteredServices =
    services &&
    services.filter(service =>
      // serviceSearch should already be lower case
      service.title.toLowerCase().includes(serviceSearch.toLowerCase())
    );

  const displayedService =
    user &&
    user.services.find(service => {
      return service.id === selectedSelectedService;
    });

  return (
    <Container>
      <div className="row">
        <div className="col-3">
          <h2> Business Services </h2>
          <div style={{ border: '1px solid gray' }}>
            <h4>Search for Services</h4>
            <input
              type="text"
              placeholder="Search"
              value={serviceSearch}
              onChange={e => {
                setServiceSearch(e.target.value);
                // Clear the selected service when the search changes
                setSelectedService(undefined);
              }}
            />
            <ServiceList
              services={filteredServices}
              selectedService={selectedService}
              setSelectedService={setSelectedService}
              setSelectedServices={setSelectedServices}
            />
          </div>
          <br />
          <div style={{ border: '1px solid gray' }}>
            <h4>Selected Services</h4>
            <SelectedServicesList
              selectedServices={selectedServices}
              setSelectedServices={setSelectedServices}
              selectedSelectedService={selectedSelectedService}
              setSelectedSelectedService={setSelectedSelectedService}
            />
          </div>
        </div>
        <div className="col-9">
          <h3> Service Questions </h3>
          <div className="row">
            {displayedService
              ? displayedService.serviceQuestions.map(question => (
                  <ServiceQuestion
                    key={question.id}
                    question={question}
                    answers={user.serviceAnswers}
                  />
                ))
              : null}
          </div>
        </div>
      </div>
    </Container>
  );
};

export default BusinessService;
