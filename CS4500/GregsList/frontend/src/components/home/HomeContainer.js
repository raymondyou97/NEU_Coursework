'use es6';

import React, { PureComponent } from 'react';

import ServiceService from '../../services/ServiceService';
import ServiceCategoryService from '../../services/ServiceCategoryService';
import Home from './Home';

class HomeContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.serviceService = ServiceService.getInstance();
    this.serviceCategoryService = ServiceCategoryService.getInstance();
    this.state = {
      id: -1,
      title: '',
      description: '',
      search: { term: '', zip: '' },
      serviceCategories: [],
      tabServiceCategories: [],
      selectedTab: -1,
      loggedInUser: null,
    };
  }

  fetchLoggedInUser = () => {
    const user = localStorage.getItem('loggedInUser');
    this.setState({
      loggedInUser: user ? user : null,
    });
  };

  logOut = () => {
    localStorage.removeItem('loggedInUser');
    localStorage.removeItem('loggedInUserId');
    this.setState({
      loggedInUser: null,
    });
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

  fetchTabServiceCategories = () => {
    this.serviceCategoryService
      .findAllServiceCategories(6)
      .then(serviceCategories => {
        this.setState({
          tabServiceCategories: serviceCategories,
        });
      });
  };

  selectServiceTab = id => {
    this.setState({ selectedTab: id });
  };

  handleTermChange = term => {
    this.setState({ search: { term: term, zip: this.state.search.zip } });
  };

  handleZipChange = zip => {
    this.setState({ search: { term: this.state.search.term, zip: zip } });
  };

  handleSearch = () => {
    this.serviceService
      .search(this.state.search.term, this.state.search.zip)
      .then(services =>
        this.props.history.push({
          pathname: `/serviceprovidersearch/${services[0].id}`,
        })
      );
  };

  render() {
    return (
      <Home
        fetchServiceCategories={this.fetchServiceCategories}
        fetchTabServiceCategories={this.fetchTabServiceCategories}
        fetchLoggedInUser={this.fetchLoggedInUser}
        serviceCategories={this.state.serviceCategories}
        tabServiceCategories={this.state.tabServiceCategories}
        selectServiceTab={this.selectServiceTab}
        selectedTab={this.state.selectedTab}
        loggedInUser={this.state.loggedInUser}
        logOut={this.logOut}
        handleTermChange={this.handleTermChange}
        handleZipChange={this.handleZipChange}
        handleSearch={this.handleSearch}
      />
    );
  }
}

export default HomeContainer;
