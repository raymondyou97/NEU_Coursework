import React, { Component } from 'react';
import ServiceCategoryService from '../../services/ServiceCategoryService';

import '../../styles/serviceCategoryDetails.css';

class ServiceCategoryDetails extends Component {
  constructor(props) {
    super(props);
    this.serviceCategoryService = ServiceCategoryService.getInstance();
    this.state = {
      id: this.props.match.params.id,
      serviceCategories: [],
      title: '',
      description: '',
      popularity: '',
    };
  }

  componentDidMount() {
    this.serviceCategoryService
      .findAllServiceCategories()
      .then(serviceCategories => {
        this.setState({
          serviceCategories: serviceCategories,
        });
      });
    this.selectServiceCategory(this.state.id);
  }

  updateTitle = e => {
    this.setState({ title: e.target.value });
  };

  updateDescription = e => {
    this.setState({ description: e.target.value });
  };

  updatePopularity = e => {
    this.setState({ popularity: e.target.value });
  };

  selectServiceCategory = id => {
    this.serviceCategoryService
      .findServiceCategoryById(id)
      .then(serviceCategory => {
        this.props.history.push('/admin/service-categories/' + id);
        this.setState({
          title: serviceCategory.title,
          description: serviceCategory.description,
          popularity: serviceCategory.popularity,
        });
      });
  };

  backToServiceCategories = () => {
    this.props.history.push('/admin/service-categories/');
  };

  createUser = () => {
    const { title, description, popularity } = this.state;

    if (title && description && popularity) {
      this.serviceCategoryService
        .createServiceCategory({
          title,
          description,
          popularity,
        })
        .then(response => {
          this.props.history.push('/admin/service-categories/');
        });
    }
  };

  deleteServiceCategory = id => {
    this.serviceCategoryService.deleteServiceCategory(id).then(response => {
      this.props.history.push('/admin/service-categories/');
    });
  };

  updateServiceCategory = () => {
    const { id, title, description, popularity } = this.state;
    let serviceCategoryData = {
      id,
      title,
      description,
      popularity,
    };
    this.serviceCategoryService
      .updateServiceCategory(id, serviceCategoryData)
      .then(response => {
        alert('Service category updated!');
      });
  };

  render() {
    return (
      <div className="service-category-detail-container">
        <h3 className="service-category-detail-sc-title">{this.state.title}</h3>
        <span className="service-category-detail-row">
          <span className="service-category-detail-title">
            Service Categories
          </span>
          <span className="service-category-detail-input">
            <select
              value={this.state.id}
              onChange={e => this.selectServiceCategory(e.target.value)}
              className="form-control"
            >
              {this.state.serviceCategories.map(serviceCategory => {
                return (
                  <option value={serviceCategory.id} key={serviceCategory.id}>
                    {serviceCategory.title}
                  </option>
                );
              })}
            </select>
          </span>
        </span>
        <span className="service-category-detail-row">
          <span className="service-category-detail-title">Title</span>
          <span className="service-category-detail-input">
            <input
              onChange={this.updateTitle}
              className="form-control"
              value={this.state.title}
            />
          </span>
        </span>
        <span className="service-category-detail-row">
          <span className="service-category-detail-title">Description</span>
          <span className="service-category-detail-input">
            <input
              onChange={this.updateDescription}
              className="form-control"
              value={this.state.description ? this.state.description : ''}
            />
          </span>
        </span>
        <span className="service-category-detail-row">
          <span className="service-category-detail-title">Popularity</span>
          <span className="service-category-detail-input">
            <input
              onChange={this.updatePopularity}
              className="form-control"
              value={this.state.popularity ? this.state.popularity : ''}
            />
          </span>
        </span>
        <span className="service-category-detail-buttons">
          <button
            className="service-category-detail-cancel"
            onClick={this.backToServiceCategories}
          >
            Cancel
          </button>
          <button
            className="service-category-detail-delete"
            onClick={() => this.deleteServiceCategory(this.state.id)}
          >
            Delete
          </button>
          <button
            className="service-category-detail-create"
            onClick={this.createServiceCategory}
          >
            Create
          </button>
          <button
            className="service-category-detail-update"
            onClick={this.updateServiceCategory}
          >
            Update
          </button>
        </span>
      </div>
    );
  }
}

export default ServiceCategoryDetails;
