import React from 'react';
import '../../styles/profiles.css';

const ProviderProfile = ({ provider }) => (
  <div>
    <div className="header">
      <div className="header-links">
        <a className="link" href="SignUp">
          Sign up
        </a>
        <a className="link" href="LogIn">
          Log in
        </a>
      </div>
    </div>
    <br />
    <br />
    <ul className="nav nav-pills">
      <li className="nav-item">
        <a className="nav-link" href="#about">
          About
        </a>
      </li>
      <li className="nav-item">
        <a className="nav-link" href="#reviews">
          Reviews
        </a>
      </li>
      <li className="nav-item">
        <a className="nav-link" href="#faqs">
          FAQs
        </a>
      </li>
    </ul>
    <div className="row">
      <div className="image-container">
        <img src="/images/skywhale.jpg" alt="..." width="300px" />
      </div>
      <div className="about-info-container">
        <h3>
          {provider.title
            ? provider.title
            : provider.firstName + ' ' + provider.lastName}
        </h3>
        {provider.reviewsOfMe.length > 0
          ? provider.reviewsOfMe
              .map(review => review.rating)
              .reduce((a, b) => a + b, 0) / provider.reviewsOfMe.length
          : 'No reviews '}
        ({provider.reviewsOfMe ? provider.reviewsOfMe.length : ''})
        <div className="list-container">
          <div className="overview">
            <h5> Overview </h5>
            <li>
              {' '}
              Hired {provider.timesHired ? provider.timesHired : 0} times{' '}
            </li>
            <li>
              {provider.backgroundChecked
                ? 'Background checked'
                : 'Background not checked'}
            </li>
            <li> {provider.employees ? provider.employees : 0} Employee(s) </li>
            <li>
              {provider.businessCreationDate
                ? new Date().getFullYear() -
                  new Date(provider.businessCreationDate).getFullYear()
                : 0}{' '}
              year(s) in business
            </li>
          </div>
          <div className="payment">
            <h5> Payment methods </h5>
            {provider.businessPaymentMethods
              ? provider.businessPaymentMethods
              : 'No specified payment methods listed, contact provider.'}
          </div>
        </div>
      </div>
    </div>
    <div className="main-body">
      {provider.introduction ? (
        <p>{provider.introduction}</p>
      ) : (
        <p>This service is really awesome and you should totally buy it.</p>
      )}
    </div>
  </div>
);

export default ProviderProfile;
