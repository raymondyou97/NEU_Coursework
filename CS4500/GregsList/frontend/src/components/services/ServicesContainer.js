'use es6';

import React, { PureComponent } from 'react';

import ServiceService from '../../services/ServiceService';
import Services from './Services';

class ServicesContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.serviceService = ServiceService.getInstance();
    this.state = {
      services: [],
      newTitle: '',
      selectedId: -1,
    };
  }

  createService = () => {
    this.serviceService
      .createService({
        title: this.state.newTitle,
      })
      .then(respData => {
        this.setState(prevState => ({
          services: prevState.services.concat(respData),
          newTitle: '',
          selectedId: -1,
        }));
      });
  };

  deleteService = id => {
    this.serviceService.deleteService(id).then(response => {
      if (response.status === 200) {
        let newServices = this.state.services.filter(service => {
          return service.id !== id;
        });
        this.setState({ services: newServices });
      } else {
        console.log(`Failed to delete service with id: ${id}`);
      }
    });
  };

  enableEdits = (id, title) => {
    this.setState({ newTitle: title, selectedId: id });
  };

  findAllServices = () => {
    this.serviceService.findAllServices().then(services => {
      this.setState({ services: services });
    });
  };

  handleTitleChange = title => {
    this.setState({ newTitle: title });
  };

  showService = id => {
    this.props.history.push(`/admin/services/${id}`);
  };

  updateService = () => {
    if (this.state.selectedId !== -1) {
      let serviceUpdate = {
        id: this.state.selectedId,
        title: this.state.newTitle,
      };
      this.serviceService
        .updateService(this.state.selectedId, serviceUpdate)
        .then(respData => {
          let newServices = [];
          this.state.services.forEach(service => {
            if (service.id === this.state.selectedId) {
              newServices.push(serviceUpdate);
            } else {
              newServices.push(service);
            }
          });
          this.setState({
            services: newServices,
            newTitle: '',
            selectedId: -1,
          });
        });
    } else {
      console.log('Must have selected a row to update.');
    }
  };

  render() {
    const { newTitle } = this.state;

    return (
      <Services
        newTitle={newTitle}
        findAllServices={this.findAllServices}
        enableEdits={this.enableEdits}
        services={this.state.services}
        handleTitleChange={this.handleTitleChange}
        createService={this.createService}
        showService={this.showService}
        deleteService={this.deleteService}
        updateService={this.updateService}
      />
    );
  }
}

export default ServicesContainer;
