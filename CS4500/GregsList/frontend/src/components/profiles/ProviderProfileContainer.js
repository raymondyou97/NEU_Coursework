import React from 'react';
import ProviderProfile from './ProviderProfile';
import UserService from '../../services/UserService';

class ProviderContainer extends React.Component {
  constructor(props) {
    super(props);
    const userId = window.location.pathname.split('/')[2];
    this.state = {
      provider: {
        username: '',
        reviewsOfMe: [],
        frequentlyAskedAnswers: [],
      },
      userId: userId,
    };
    this.userService = UserService.getInstance();
  }
  componentDidMount() {
    this.userService
      .findUserById(this.state.userId)
      .then(provider => this.setState({ provider: provider }));
  }
  render() {
    return <ProviderProfile provider={this.state.provider} />;
  }
}

export default ProviderContainer;
