import React from 'react';
import Button from 'react-bootstrap/Button';
import InputGroup from 'react-bootstrap/InputGroup';
import FormControl from 'react-bootstrap/FormControl';

export default class ServiceProviderSearch extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      searchProviderName: '',
      searchZipCode: '',
    };
  }

  handleSearchProviderNameChange = e => {
    this.setState({ searchProviderName: e.target.value });
  };

  handleSearchZipCodeChange = e => {
    this.setState({ searchZipCode: e.target.value });
  };

  handleSearchSubmission = () => {
    let providers = this.props.serviceProviders;
    if (this.state.searchProviderName !== '') {
      providers = providers.filter(provider =>
        provider.firstName
          .concat(' ' + provider.lastName)
          .includes(this.state.searchProviderName)
      );
    }
    if (this.state.searchZipCode !== '') {
      providers = providers.filter(
        provider => provider.zipCode.toString() === this.state.searchZipCode
      );
    }
    this.props.updateSearchServiceProviders(providers);
  };

  render() {
    return (
      <div className="search-section">
        <InputGroup className="search-bars">
          <FormControl
            onChange={this.handleSearchProviderNameChange}
            placeholder="Search for providers"
            value={this.state.searchProviderName}
          />
          <FormControl
            onChange={this.handleSearchZipCodeChange}
            placeholder="Zip code"
            value={this.state.searchZipCode}
          />
          <InputGroup.Append>
            <Button
              onClick={this.handleSearchSubmission}
              className="search-button"
              variant="primary"
            >
              Search
            </Button>
          </InputGroup.Append>
        </InputGroup>
      </div>
    );
  }
}
