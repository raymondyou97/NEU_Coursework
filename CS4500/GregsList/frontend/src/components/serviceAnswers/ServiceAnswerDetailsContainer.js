import React, { PureComponent } from 'react';
import ServiceAnswerService from '../../services/ServiceAnswerService';
import ServiceAnswerDetails from './ServiceAnswerDetails';

export default class ServiceAnswerDetailsContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.serviceAnswerService = ServiceAnswerService.getInstance();
    this.state = {
      id: this.props.match.params.id,
      serviceAnswers: [],
      serviceAnswer: {
        trueFalseAnswer: '',
        maxRangeAnswer: '',
        minRangeAnswer: '',
        choiceAnswer: '',
        id: '',
      },
    };

    this.fetchServiceAnswer = this.fetchServiceAnswer.bind(this);
    this.selectServiceAnswer = this.selectServiceAnswer.bind(this);
    this.handleTrueFalseChange = this.handleTrueFalseChange.bind(this);
    this.handleMaxRangeAnswer = this.handleMaxRangeAnswer.bind(this);
    this.handleMinRangeAnswer = this.handleMinRangeAnswer.bind(this);
    this.handleChoiceAnswer = this.handleChoiceAnswer.bind(this);
    this.backToAnswers = this.backToAnswers.bind(this);
    this.createServiceAnswer = this.createServiceAnswer.bind(this);
    this.deleteServiceAnswer = this.deleteServiceAnswer.bind(this);
    this.updateServiceAnswer = this.updateServiceAnswer.bind(this);
  }

  fetchServiceAnswer() {
    this.serviceAnswerService.findAllServiceAnswers().then(serviceAnswers => {
      this.setState({
        serviceAnswers: serviceAnswers,
      });
    });
    this.selectServiceAnswer(this.state.id);
  }

  selectServiceAnswer = id => {
    this.serviceAnswerService.findServiceAnswerById(id).then(serviceAnswer => {
      this.props.history.push('/admin/service-answers/' + id);
      this.setState({
        serviceAnswer: serviceAnswer,
      });
    });
  };

  handleTrueFalseChange = e => {
    let bool = e.target.value.toLowerCase() === 'true';
    this.setState({
      serviceAnswer: {
        trueFalseAnswer: bool,
        maxRangeAnswer: this.state.serviceAnswer.maxRangeAnswer,
        minRangeAnswer: this.state.serviceAnswer.minRangeAnswer,
        choiceAnswer: this.state.serviceAnswer.choiceAnswer,
      },
    });
  };

  handleMaxRangeAnswer = e => {
    this.setState({
      serviceAnswer: {
        maxRangeAnswer: e.target.value,
        trueFalseAnswer: this.state.serviceAnswer.trueFalseAnswer,
        minRangeAnswer: this.state.serviceAnswer.minRangeAnswer,
        choiceAnswer: this.state.serviceAnswer.choiceAnswer,
      },
    });
  };

  handleMinRangeAnswer = e => {
    this.setState({
      serviceAnswer: {
        minRangeAnswer: e.target.value,
        trueFalseAnswer: this.state.serviceAnswer.trueFalseAnswer,
        maxRangeAnswer: this.state.serviceAnswer.maxRangeAnswer,
        choiceAnswer: this.state.serviceAnswer.choiceAnswer,
      },
    });
  };

  handleChoiceAnswer = e => {
    this.setState({
      serviceAnswer: {
        choiceAnswer: e.target.value,
        trueFalseAnswer: this.state.serviceAnswer.trueFalseAnswer,
        maxRangeAnswer: this.state.serviceAnswer.maxRangeAnswer,
        minRangeAnswer: this.state.serviceAnswer.minRangeAnswer,
      },
    });
  };

  backToAnswers = () => {
    this.props.history.push('/admin/service-answers/');
  };

  createServiceAnswer = () => {
    this.serviceAnswerService
      .createServiceAnswer({
        trueFalseAnswer: this.state.serviceAnswer.trueFalseAnswer,
        maxRangeAnswer: this.state.serviceAnswer.maxRangeAnswer,
        minRangeAnswer: this.state.serviceAnswer.minRangeAnswer,
        choiceAnswer: this.state.serviceAnswer.choiceAnswer,
      })
      .then(response => {
        this.props.history.push('/admin/service-answers/');
      });
  };

  updateServiceAnswer = () => {
    let newServiceAnswer = {
      id: parseInt(this.state.id),
      trueFalseAnswer: this.state.serviceAnswer.trueFalseAnswer,
      minRangeAnswer: this.state.serviceAnswer.minRangeAnswer,
      maxRangeAnswer: this.state.serviceAnswer.maxRangeAnswer,
      choiceAnswer: this.state.serviceAnswer.choiceAnswer,
    };

    this.serviceAnswerService
      .updateServiceAnswer(this.state.id, newServiceAnswer)
      .then(response => {
        this.props.history.push('/admin/service-answers/');
      });
  };

  deleteServiceAnswer = id =>
    this.serviceAnswerService.deleteServiceAnswer(id).then(response => {
      if (response.status === 200) {
        this.props.history.push('/admin/service-answers/');
      } else {
        console.log(`Failed to delete service answer with id: ${id}`);
      }
    });

  render() {
    const { id, serviceAnswers, serviceAnswer } = this.state;

    return (
      <ServiceAnswerDetails
        id={id}
        serviceAnswers={serviceAnswers}
        serviceAnswer={serviceAnswer}
        fetchServiceAnswer={this.fetchServiceAnswer}
        selectServiceAnswer={this.selectServiceAnswer}
        handleTrueFalseChange={this.handleTrueFalseChange}
        handleMinRangeAnswer={this.handleMinRangeAnswer}
        handleMaxRangeAnswer={this.handleMaxRangeAnswer}
        handleChoiceAnswer={this.handleChoiceAnswer}
        backToAnswers={this.backToAnswers}
        createServiceAnswer={this.createServiceAnswer}
        deleteServiceAnswer={this.deleteServiceAnswer}
        updateServiceAnswer={this.updateServiceAnswer}
      />
    );
  }
}
