import React, { Component } from 'react';
import './App.css';
import { BrowserRouter as Router, Route } from 'react-router-dom';
import { Navbar, Nav } from 'react-bootstrap';
import Admin from './components/Admin';
import BusinessService from './components/businessService/BusinessService';
import HomeContainer from './components/home/HomeContainer';
import RegisterContainer from './components/login/RegisterContainer';
import serviceProviderSearchIndex from './components/serviceProviderSearch/Index';
import ServiceNavigator from './components/serviceNavigator/ServiceNavigator';
import LoginContainer from './components/login/LoginContainer';
import BusinessIndex from './components/business/Index';
import ProviderProfileContainer from './components/profiles/ProviderProfileContainer';
import ProfileEditContainer from './components/profile/ProfileEditContainer';

class App extends Component {
  renderNavigation() {
    return (
      <div className="container">
        <Navbar bg="primary" variant="dark" expand="lg">
          <Navbar.Brand href="/">Gregslist</Navbar.Brand>
          <Navbar.Toggle
            className="header-btn-nav"
            aria-controls="basic-navbar-nav"
          />
          <Navbar.Collapse id="basic-navbar-nav">
            <Nav className="mr-auto">
              <Nav.Link href="/">Home</Nav.Link>
              <Nav.Link href="/services">Services</Nav.Link>
              <Nav.Link href="/ServiceProviderSearch/122">Providers</Nav.Link>
              <Nav.Link href="/business">Business</Nav.Link>
              <Nav.Link href="/businessService">Business Services</Nav.Link>
              <Nav.Link href="/MyProfile">Profile</Nav.Link>
            </Nav>
          </Navbar.Collapse>
        </Navbar>
        <br />
      </div>
    );
  }

  render() {
    return (
      <div className="App">
        {this.renderNavigation()}
        <Router>
          <div>
            <Route path="/" exact component={HomeContainer} />
            <Route path="/admin" component={Admin} />
            <Route
              path="/ServiceProviderSearch/:id"
              component={serviceProviderSearchIndex}
            />
            <Route path="/provider/:id" component={ProviderProfileContainer} />
            <Route path="/SignUp" component={RegisterContainer} />
            <Route path="/LogIn" component={LoginContainer} />
            <Route path="/services" component={ServiceNavigator} />
            <Route path="/business" component={BusinessIndex} />
            <Route path="/businessService" component={BusinessService} />
            <Route path="/MyProfile" component={ProfileEditContainer} />
          </div>
        </Router>
      </div>
    );
  }
}

export default App;
