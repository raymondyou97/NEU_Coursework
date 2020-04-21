import React from 'react';
import UserService from '../../services/UserService';
import ServiceService from '../../services/ServiceService';
import ServiceProviderFilter from './ServiceProviderFilter';
import ServiceProviderResult from './ServiceProviderResult';

import CardGroup from 'react-bootstrap/CardGroup';
import { Link } from 'react-router-dom';

import '../../styles/serviceProviders.css';
import ServiceProviderSearch from './ServiceProviderSearch';

class serviceProviderSearchIndex extends React.Component {
  constructor(props) {
    super(props);
    this.serviceService = ServiceService.getInstance();
    this.userService = UserService.getInstance();
    this.state = {
      searchPredicates: [],
      serviceProviders: [],
      searchServiceProviders: [],
    };
  }

  componentDidMount() {
    this.fetchServiceQuestions();
    this.fetchServiceProviders();
  }

  fetchServiceQuestions = () => {
    this.serviceService
      .findAllServiceQuestionsForService(this.props.match.params.id)
      .then(questions => {
        this.setState({
          searchPredicates: questions.map(question => {
            return {
              serviceQuestion: question,
              serviceAnswer: {},
            };
          }),
        });
      });
  };

  fetchServiceProviders = () => {
    this.serviceService
      .findAllProvidersForService(this.props.match.params.id)
      .then(providers => {
        if (providers) {
          this.setState({
            serviceProviders: providers,
            searchServiceProviders: providers,
          });
        }
      });
  };

  fetchFilteredServiceProviders = searchPredicates => {
    this.serviceService
      .findServiceById(this.props.match.params.id)
      .then(service => {
        this.userService
          .findUsersForSearch({
            service: service,
            searchPredicates: searchPredicates,
          })
          .then(providers => {
            this.setState({
              serviceProviders: providers,
              searchServiceProviders: providers,
              searchPredicates: searchPredicates,
            });
          });
      });
  };

  updateSearchServiceProviders = searchServiceProviders => {
    this.setState({ searchServiceProviders: searchServiceProviders });
  };

  goToProfile = id => {
    this.props.history.push(`/provider/${id}`);
  };

  render() {
    let results = '';
    if (Array.isArray(this.state.searchServiceProviders)) {
      results = this.state.searchServiceProviders.map(provider => (
        <ServiceProviderResult
          serviceProvider={provider}
          goToProfile={() => this.goToProfile(provider.id)}
        />
      ));
    }

    return (
      <div className="service-provider-search">
        <div className="header">
          <ServiceProviderSearch
            serviceProviders={this.state.serviceProviders}
            updateSearchServiceProviders={this.updateSearchServiceProviders}
          />
          <div className="header-links">
            <Link className="link" to="/SignUp">
              Sign up
            </Link>
            <Link className="link" to="/LogIn">
              Log in
            </Link>
          </div>
        </div>
        <div className="search-provider-body">
          <div className="search-provider-filter">
            <ServiceProviderFilter
              searchPredicates={this.state.searchPredicates}
              fetchFilteredServiceProviders={this.fetchFilteredServiceProviders}
            />
          </div>
          <div className="search-provider-results">
            <CardGroup style={{ display: 'flex', flexDirection: 'column' }}>
              {results}
            </CardGroup>
          </div>
        </div>
      </div>
    );
  }
}

export default serviceProviderSearchIndex;
