import React from 'react';
import ServiceService from '../../services/ServiceService';

import '../../styles/services/serviceDetails.css';

class ServiceDetails extends React.Component {
  constructor(props) {
    super(props);

    this.serviceService = ServiceService.getInstance();
    this.state = {
      services: [],
      title: '',
      id: this.props.match.params.id,
    };
  }

  componentDidMount() {
    this.serviceService.findAllServices().then(services => {
      this.props.history.push('/admin/services/' + services[0].id);
      this.setState({
        services: services,
      });
    });
    this.selectService(this.state.id);
  }

  selectService = id =>
    this.serviceService.findServiceById(id).then(service => {
      this.props.history.push('/admin/services/' + id);
      this.setState({
        title: service.title,
        id: service.id,
      });
    });

  backToServices = () => {
    this.props.history.push('/admin/services/');
  };

  updateTitle = e => {
    this.setState({ title: e.target.value });
  };

  deleteService = id => {
    this.serviceService.deleteService(id).then(response => {
      if (response.status === 200) {
        this.props.history.push('/admin/services/');
      } else {
        console.log(`Failed to delete service with id ${id}`);
      }
    });
  };

  updateService = () => {
    const { id, title } = this.state;
    let serviceData = { id, title };
    this.serviceService.updateService(id, serviceData).then(response => {
      let newServices = [];
      this.state.services.forEach(service => {
        if (service.id === id) {
          newServices.push(serviceData);
        } else {
          newServices.push(service);
        }
      });
      this.setState({ services: newServices });
      alert('Service updated.');
    });
  };

  render() {
    return (
      <div className="service-detail-container">
        <h3 className="service-detail-header">{this.state.title}</h3>
        <span className="service-detail-row">
          <span className="user-detail-title">Services</span>
          <span className="service-detail-input">
            <select
              value={this.state.id}
              onChange={e => this.selectService(e.target.value)}
              className="form-control"
            >
              {this.state.services.map(service => (
                <option value={service.id} key={service.id}>
                  {service.title}
                </option>
              ))}
            </select>
          </span>
        </span>
        <span className="service-detail-row">
          <span className="service-detail-title">Title</span>
          <span className="service-detail-input">
            <input
              onChange={this.updateTitle}
              className="form-control"
              value={this.state.title}
            />
          </span>
        </span>
        <span className="service-detail-buttons">
          <button
            className="service-detail-cancel"
            onClick={this.backToServices}
          >
            Cancel
          </button>
          <button
            className="service-detail-delete"
            onClick={() => this.deleteService(this.state.id)}
          >
            Delete
          </button>
          <button
            className="service-detail-update"
            onClick={this.updateService}
          >
            Update
          </button>
        </span>
      </div>
    );
  }
}

export default ServiceDetails;
