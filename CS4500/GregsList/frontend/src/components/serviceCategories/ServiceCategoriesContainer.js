'use es6';

import React, { PureComponent } from 'react';

import ServiceCategoryService from '../../services/ServiceCategoryService';
import ServiceCategories from './ServiceCategories';

class ServiceCategoriesContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.serviceCategoryService = ServiceCategoryService.getInstance();
    this.state = {
      id: -1,
      title: '',
      description: '',
      serviceCategories: [],
    };
  }

  updateTitle = title => {
    this.setState({ title });
  };

  updateDescription = description => {
    this.setState({ description });
  };

  updateId = id => {
    this.setState({ id });
  };

  fetchServiceCategories = () => {
    this.serviceCategoryService
      .findAllServiceCategories()
      .then(serviceCategories => {
        this.setState({
          serviceCategories: serviceCategories,
        });
      });
  };

  createServiceCategory = () => {
    const { title, description, serviceCategories } = this.state;

    if (title && description) {
      let titleConflict = false;
      this.state.serviceCategories.forEach(category => {
        if (title === category.title) {
          titleConflict = true;
        }
      });
      if (titleConflict) {
        alert(
          "Can't create service category with the same title as another service category"
        );
      } else {
        this.serviceCategoryService
          .createServiceCategory({
            title,
            description,
          })
          .then(response => {
            this.setState({
              id: -1,
              title: '',
              description: '',
              serviceCategories: serviceCategories.concat(response),
            });
          });
      }
    }
  };

  deleteServiceCategory = id => {
    this.serviceCategoryService.deleteServiceCategory(id);
    const newServiceCategories = this.state.serviceCategories.filter(sc => {
      return sc.id !== id;
    });
    this.setState({
      serviceCategories: newServiceCategories,
    });
  };

  // editServiceCategory = (id, title, description) => {
  //   this.setState({
  //     id,
  //     title,
  //     description,
  //   })
  // };

  updateServiceCategory = () => {
    const { id, title, description } = this.state;
    if (id !== -1 && title && description) {
      let titleConflict = false;
      this.state.serviceCategories.forEach(category => {
        if (title === category.title && id !== category.id) {
          titleConflict = true;
        }
      });
      if (titleConflict) {
        alert(
          "Can't create service category with the same title as another service category"
        );
      } else {
        this.serviceCategoryService.updateServiceCategory(id, {
          id,
          title,
          description,
        });
        let newServiceCategories = this.state.serviceCategories;
        newServiceCategories.forEach((val, ind) => {
          if (val.id === id) {
            newServiceCategories[ind] = {
              id,
              title,
              description,
            };
          }
        });
        this.setState({
          id: -1,
          title: '',
          description: '',
        });
      }
    }
  };

  showDetails = id => {
    this.props.history.push(`/admin/service-categories/${id}`);
  };

  render() {
    const { title, description } = this.state;

    const serviceCategory = {
      title,
      description,
    };

    return (
      <ServiceCategories
        fetchServiceCategories={this.fetchServiceCategories}
        serviceCategory={serviceCategory}
        updateId={this.updateId}
        serviceCategories={this.state.serviceCategories}
        updateTitle={this.updateTitle}
        updateDescription={this.updateDescription}
        createServiceCategory={this.createServiceCategory}
        showDetails={this.showDetails}
        deleteServiceCategory={this.deleteServiceCategory}
        updateServiceCategory={this.updateServiceCategory}
      />
    );
  }
}

export default ServiceCategoriesContainer;
