import React from 'react';

import Card from 'react-bootstrap/Card';
import Button from 'react-bootstrap/Button';
import '../../styles/serviceProviders.css';

export default class ServiceProviderResult extends React.Component {
  render() {
    let {
      firstName,
      lastName,
      introduction,
      businessCreationDate,
      timesHired,
      title,
      reviewsOfMe,
    } = this.props.serviceProvider;
    let description = 'No description given by this service provider.';
    if (introduction) {
      description = introduction;
    }
    const today = new Date();
    const curYear = today.getFullYear();
    let yearsSinceCreation = 0;
    if (businessCreationDate) {
      yearsSinceCreation = curYear - businessCreationDate.getFullYear();
    }
    if (!timesHired) {
      timesHired = 0;
    }
    if (!title) {
      title = firstName + ' ' + lastName;
    }
    let averageReviewScore = 0.0;
    if (reviewsOfMe.length > 0) {
      averageReviewScore =
        reviewsOfMe.map(review => review.rating).reduce((a, b) => a + b, 0) /
        reviewsOfMe.length;
    }
    const defaultPrice = '$0';
    const reviewText =
      averageReviewScore +
      ' average rating, ' +
      reviewsOfMe.length +
      ' reviews\n';
    const businessText =
      yearsSinceCreation + ' years in business, ' + timesHired + ' hires\n';

    let img = this.props.image;
    if (this.props.image == null) {
      img = '/images/skywhale.jpg';
    }
    return (
      <Card className="provider-result-card" style={{ flex: 1 }}>
        <Card.Img
          className="provider-result-card-img-left"
          variant="left"
          src={img}
        />
        <Card.Body className="provider-result-card-body">
          <div className="result-left">
            <Card.Title className="provider-result-card-title">
              {title}
            </Card.Title>
            <Card.Text className="description-text">{reviewText}</Card.Text>
            <Card.Text className="description-text">{businessText}</Card.Text>
            <Card.Text className="description-text">{description}</Card.Text>
          </div>
          <div className="result-right">
            <text className="price-text">{defaultPrice}</text>
            <Button
              variant="primary"
              onClick={this.props.goToProfile}
              className="view-profile-button"
            >
              View Profile
            </Button>
          </div>
        </Card.Body>
      </Card>
    );
  }
}
