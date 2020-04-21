import React from 'react';
import '../../styles/business.css';
import BusinessAddress from './Address';
import BusinessGeneral from './General';
import BusinessSocial from './Social';
import BusinessPayment from './Payment';
import UserService from '../../services/UserService';

class BusinessIndex extends React.Component {
  constructor(props) {
    super(props);
    this.userService = UserService.getInstance();
    this.state = {
      id: '',
      title: '',
      businessYearFounded: '',
      employees: '',
      businessEmail: '',
      businessAddressStreet: '',
      businessAddressCity: '',
      businessAddressState: '',
      businessAddressZip: '',
      businessPaymentMethods: '',
      businessFacebookURL: '',
      businessInstagramURL: '',
      businessTwitterURL: '',
    };
  }

  componentDidMount() {
    let userId = localStorage.getItem('loggedInUserId');
    if (userId) {
      this.userService.findUserById(Number(userId)).then(user => {
        this.setState(user);
      });
    }
  }

  saveProfile() {
    this.userService.updateUser(this.state.id, this.state).then(data => {
      if (data.error) {
        alert('Error');
      } else {
        alert('Success');
        this.props.history.push('/MyProfile');
      }
    });
  }

  getBusinessName = name => {
    this.setState({ title: name });
  };

  getYearFounded = year => {
    this.setState({ businessYearFounded: year });
  };

  getNumEmployees = numEmployees => {
    this.setState({ employees: numEmployees });
  };

  getEmail = email => {
    this.setState({ businessEmail: email });
  };

  getStreet = street => {
    this.setState({ businessAddressStreet: street });
  };

  getCity = city => {
    this.setState({ businessAddressCity: city });
  };

  getState = state => {
    this.setState({ businessAddressState: state });
  };

  getZip = zip => {
    this.setState({ businessAddressZip: zip });
  };

  getPaymentOptions = paymentOptions => {
    let newPaymentOptions = Array.from(paymentOptions).join(',');
    this.setState({ businessPaymentMethods: newPaymentOptions });
  };

  getFacebookURL = facebookURL => {
    this.setState({ businessFacebookURL: facebookURL });
  };

  getInstagramURL = instagramURL => {
    this.setState({ businessInstagramURL: instagramURL });
  };

  getTwitterURL = twitterURL => {
    this.setState({ businessTwitterURL: twitterURL });
  };

  render() {
    return (
      <div className="container ">
        <h1>Business</h1>
        <div className="business-profile-container">
          <div className="general-and-address">
            <BusinessGeneral
              initialState={this.state}
              businessName={this.getBusinessName}
              yearFounded={this.getYearFounded}
              numEmployees={this.getNumEmployees}
              email={this.getEmail}
            />
            <br />
            <BusinessAddress
              initialState={this.state}
              street={this.getStreet}
              city={this.getCity}
              state={this.getState}
              zip={this.getZip}
            />
          </div>
          <div className="payment-and-social">
            <BusinessPayment
              initialState={this.state}
              paymentOptions={this.getPaymentOptions}
            />
            <br />
            <BusinessSocial
              initialState={this.state}
              facebookURL={this.getFacebookURL}
              instagramURL={this.getInstagramURL}
              twitterURL={this.getTwitterURL}
            />
            <div className="business-save-btn-container">
              <button
                className="btn btn-success business-save-btn"
                onClick={() => this.saveProfile()}
              >
                Save
              </button>
            </div>
          </div>
        </div>
      </div>
    );
  }
}

export default BusinessIndex;
