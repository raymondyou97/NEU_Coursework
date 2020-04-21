import React from 'react';

import Button from 'react-bootstrap/Button';
import InputGroup from 'react-bootstrap/InputGroup';
import FormControl from 'react-bootstrap/FormControl';
import ButtonGroup from 'react-bootstrap/ButtonGroup';

import '../../styles/home.css';

class Home extends React.PureComponent {
  componentDidMount() {
    this.props.fetchServiceCategories();
    this.props.fetchTabServiceCategories(6);
    this.props.fetchLoggedInUser();
  }

  handleTermChange = e => {
    this.props.handleTermChange(e.target.value);
  };

  handleZipChange = e => {
    this.props.handleZipChange(e.target.value);
  };

  renderHeader() {
    const { loggedInUser, logOut } = this.props;

    const links = loggedInUser ? (
      <div className="header-links">
        <span className="user-name">Welcome {loggedInUser}!</span>
        <span className="log-out" onClick={logOut}>
          Log out
        </span>
      </div>
    ) : (
      <div className="header-links">
        <a className="link" href="SignUp">
          Sign up
        </a>
        <a className="link" href="LogIn">
          Log in
        </a>
      </div>
    );

    return (
      <div className="header">
        <h1>Find professionals near you</h1>
        {links}
      </div>
    );
  }

  renderSearchSection() {
    return (
      <div className="search-section">
        <InputGroup className="search-bars">
          <FormControl
            placeholder="Search for providers"
            onChange={this.handleTermChange}
          />
          <FormControl placeholder="Zip code" onChange={this.handleZipChange} />
          <InputGroup.Append>
            <Button
              className="search-button"
              variant="primary"
              onClick={() => this.props.handleSearch()}
            >
              Search
            </Button>
          </InputGroup.Append>
        </InputGroup>
      </div>
    );
  }

  renderServiceButtons() {
    const { serviceCategories } = this.props;

    if (!(serviceCategories && serviceCategories.length)) return null;

    return (
      <div className="service-categories-container">
        <ButtonGroup className="service-categories">
          {serviceCategories[0] ? (
            <Button variant="link">
              <a href={`services#${serviceCategories[0].id}`}>
                <div className="service-category-button">
                  {serviceCategories[0].title}
                </div>
              </a>
            </Button>
          ) : null}
          {serviceCategories[1] ? (
            <Button variant="link">
              <a href={`services#${serviceCategories[1].id}`}>
                <div className="service-category-button">
                  {serviceCategories[1].title}
                </div>
              </a>
            </Button>
          ) : null}
          {serviceCategories[2] ? (
            <Button variant="link">
              <a href={`services#${serviceCategories[2].id}`}>
                <div className="service-category-button">
                  {serviceCategories[2].title}
                </div>
              </a>
            </Button>
          ) : null}
          {serviceCategories[3] ? (
            <Button variant="link">
              <a href={`services#${serviceCategories[3].id}`}>
                <div className="service-category-button">
                  {serviceCategories[3].title}
                </div>
              </a>
            </Button>
          ) : null}
          {serviceCategories.length > 4 ? (
            <Button variant="link">
              <a href="services">
                <div className="service-category-button">More</div>
              </a>
            </Button>
          ) : null}
        </ButtonGroup>
      </div>
    );
  }

  generateSelectedCategoryTab() {
    if (this.props.selectedTab !== -1) {
      return (
        <div className="row">
          {this.props.tabServiceCategories[this.props.selectedTab].services.map(
            (service, index) => (
              <div key={service.id} className="card col-4 no-border">
                <img
                  src="/images/skywhale.jpg"
                  className="card-img-top"
                  alt="..."
                />
                <div className="card-body">
                  <h5 className="card-title">
                    <a href={`/ServiceProviderSearch/${service.id}`}>
                      {service.title}
                    </a>
                  </h5>
                </div>
              </div>
            )
          )}
        </div>
      );
    }
  }

  renderServiceTabs() {
    const { tabServiceCategories, selectServiceTab } = this.props;

    if (!tabServiceCategories.length) return null;

    return (
      <div>
        <ul className="nav nav-tabs">
          {tabServiceCategories.map((serviceCategory, index) => (
            <li key={serviceCategory.id} className="nav-item">
              {/* eslint-disable-next-line */}
              <a
                onClick={() => selectServiceTab(index)}
                className="nav-link"
                href="#"
              >
                {serviceCategory.title}
              </a>
            </li>
          ))}
        </ul>
        {this.generateSelectedCategoryTab()}
        <br />
      </div>
    );
  }

  render() {
    return (
      <div className="home">
        {this.renderHeader()}
        {this.renderSearchSection()}
        {this.renderServiceButtons()}
        {this.renderServiceTabs()}
      </div>
    );
  }
}

export default Home;
