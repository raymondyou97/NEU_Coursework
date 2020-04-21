import React, { PureComponent } from 'react';
import ServiceAnswerService from '../../services/ServiceAnswerService';
import ServiceAnswers from './ServiceAnswers';

export default class ServiceAnswersContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.serviceAnswerService = ServiceAnswerService.getInstance();
    this.state = {
      serviceAnswers: [],
      trueFalseAnswer: '',
      maxRangeAnswer: '',
      minRangeAnswer: '',
      choiceAnswer: '',
      selectedId: '',
      currentPage: 0,
      totalPages: 0,
      count: 10,
    };

    this.fetchServiceAnswers = this.fetchServiceAnswers.bind(this);
    this.handleTrueFalseChange = this.handleTrueFalseChange.bind(this);
    this.handleMaxRangeAnswer = this.handleMaxRangeAnswer.bind(this);
    this.handleMinRangeAnswer = this.handleMinRangeAnswer.bind(this);
    this.handleChoiceAnswer = this.handleChoiceAnswer.bind(this);
    this.createServiceAnswer = this.createServiceAnswer.bind(this);
    this.showServiceAnswerDetails = this.showServiceAnswerDetails.bind(this);
    this.deleteServiceAnswer = this.deleteServiceAnswer.bind(this);
    this.updateServiceAnswer = this.updateServiceAnswer.bind(this);
    this.getServiceAnswerIDs = this.getServiceAnswerIDs.bind(this);
    this.pageLeft = this.pageLeft.bind(this);
    this.pageRight = this.pageRight.bind(this);
  }

  fetchServiceAnswers = () => {
    this.serviceAnswerService
      .findPagedServiceAnswers(this.state.currentPage, this.state.count)
      .then(pagedAnswers => {
        if (pagedAnswers.content) {
          this.setState({
            serviceAnswers: pagedAnswers.content,
            totalPages: pagedAnswers.totalPages,
          });
        }
      });
  };

  handleTrueFalseChange = e => {
    let bool = e.target.value.toLowerCase() === 't';
    this.setState({
      trueFalseAnswer: bool,
    });
  };

  handleMaxRangeAnswer = e => {
    this.setState({
      maxRangeAnswer: e.target.value,
    });
  };

  handleMinRangeAnswer = e => {
    this.setState({
      minRangeAnswer: e.target.value,
    });
  };

  handleChoiceAnswer = e => {
    this.setState({
      choiceAnswer: e.target.value,
    });
  };

  handleIdChange = e => {
    if (e.target.value === '-1') {
      this.setState({
        trueFalseAnswer: '',
        maxRangeAnswer: '',
        minRangeAnswer: '',
        choiceAnswer: '',
        selectedId: '',
      });
    } else {
      let serviceAnswer = this.state.serviceAnswers.find(answer => {
        return answer.id.toString() === e.target.value;
      });
      this.setState({
        trueFalseAnswer: serviceAnswer.trueFalseAnswer,
        maxRangeAnswer: serviceAnswer.maxRangeAnswer,
        minRangeAnswer: serviceAnswer.minRangeAnswer,
        choiceAnswer: serviceAnswer.choiceAnswer,
        selectedId: e.target.value,
      });
    }
  };

  handleCountChange = e => {
    let count = e.target.value;
    if (count === 'All') {
      this.serviceAnswerService.findAllServiceAnswers().then(serviceAnswers =>
        this.setState({
          serviceAnswers: serviceAnswers,
          count: count,
          totalPages: 1,
          currentPage: 0,
        })
      );
    } else {
      this.serviceAnswerService
        .findPagedServiceAnswers(0, count)
        .then(pagedAnswers => {
          if (pagedAnswers.content) {
            this.setState({
              serviceAnswers: pagedAnswers.content,
              count: count,
              totalPages: pagedAnswers.totalPages,
              currentPage: 0,
            });
          }
        });
    }
  };

  getServiceAnswerIDs() {
    let serviceAnswerIDs = [];
    //option for when you want to add new row
    serviceAnswerIDs.push(<option key={-1} value={-1} />);
    for (let i = 0; i < this.state.serviceAnswers.length; i++) {
      serviceAnswerIDs.push(
        <option
          key={this.state.serviceAnswers[i].id}
          value={this.state.serviceAnswers[i].id}
        >
          {this.state.serviceAnswers[i].id}
        </option>
      );
    }
    let serviceAnswerIDChoices = (
      <select onChange={this.handleIdChange}>{serviceAnswerIDs}</select>
    );

    return serviceAnswerIDChoices;
  }

  findAllServiceAnswers = () =>
    this.serviceAnswerService
      .findAllServiceAnswers()
      .then(serviceAnswers =>
        this.setState({ serviceAnswers: serviceAnswers })
      );

  pageLeft = () => {
    if (this.state.currentPage !== 0 && this.state.count !== 'All') {
      let currentPage = this.state.currentPage - 1;
      this.serviceAnswerService
        .findPagedServiceAnswers(currentPage, this.state.count)
        .then(pagedAnswers => {
          if (pagedAnswers.content) {
            this.setState({
              serviceAnswers: pagedAnswers.content,
              totalPages: pagedAnswers.totalPages,
              currentPage: currentPage,
            });
          }
        });
    }
  };

  pageRight = () => {
    if (
      this.state.currentPage < this.state.totalPages - 1 &&
      this.state.count !== 'All'
    ) {
      let currentPage = this.state.currentPage + 1;
      this.serviceAnswerService
        .findPagedServiceAnswers(currentPage, this.state.count)
        .then(pagedAnswers => {
          if (pagedAnswers.content) {
            this.setState({
              serviceAnswers: pagedAnswers.content,
              totalPages: pagedAnswers.totalPages,
              currentPage: currentPage,
            });
          }
        });
    }
  };

  createServiceAnswer = () => {
    this.serviceAnswerService
      .createServiceAnswer({
        trueFalseAnswer: this.state.trueFalseAnswer,
        maxRangeAnswer: this.state.maxRangeAnswer,
        minRangeAnswer: this.state.minRangeAnswer,
        choiceAnswer: this.state.choiceAnswer,
      })
      .then(respData => {
        this.setState(prevState => ({
          serviceAnswers: prevState.serviceAnswers.concat(respData),
          trueFalseAnswer: '',
          maxRangeAnswer: '',
          minRangeAnswer: '',
          choiceAnswer: '',
        }));
      });
  };

  deleteServiceAnswer = id =>
    this.serviceAnswerService.deleteServiceAnswer(id).then(response => {
      if (response.status === 200) {
        let newServiceAnswers = this.state.serviceAnswers.filter(answer => {
          return answer.id !== id;
        });
        this.setState({
          serviceAnswers: newServiceAnswers,
        });
      } else {
        console.log(`Failed to delete service answer with id: ${id}`);
      }
    });

  findServiceAnswerById = id =>
    this.serviceAnswerService.findServiceAnswerById(id).then(serviceAnswer =>
      this.setState({
        serviceAnswer: serviceAnswer,
      })
    );

  updateServiceAnswer = () => {
    if (this.state.selectedId !== '') {
      let newServiceAnswer = {
        id: parseInt(this.state.selectedId),
        trueFalseAnswer: this.state.trueFalseAnswer,
        minRangeAnswer: this.state.minRangeAnswer,
        maxRangeAnswer: this.state.maxRangeAnswer,
        choiceAnswer: this.state.choiceAnswer,
      };

      this.serviceAnswerService
        .updateServiceAnswer(this.state.selectedId, newServiceAnswer)
        .then(response => {
          let newServiceAnswers = [];
          this.state.serviceAnswers.forEach(answer => {
            if (answer.id.toString() === this.state.selectedId) {
              newServiceAnswers.push(newServiceAnswer);
            } else {
              newServiceAnswers.push(answer);
            }
          });
          this.setState({
            serviceAnswers: newServiceAnswers,
            trueFalseAnswer: '',
            maxRangeAnswer: '',
            minRangeAnswer: '',
            choiceAnswer: '',
            selectedId: '',
          });
        });
    } else {
      console.log('select a id first');
    }
  };

  showServiceAnswerDetails(id) {
    this.props.history.push(`/admin/service-answers/${id}`);
  }

  render() {
    const {
      serviceAnswers,
      trueFalseAnswer,
      maxRangeAnswer,
      minRangeAnswer,
      choiceAnswer,
    } = this.state;
    const selectedServiceAnswer = {
      trueFalseAnswer,
      maxRangeAnswer,
      minRangeAnswer,
      choiceAnswer,
    };
    const serviceAnswerIds = this.getServiceAnswerIDs();

    return (
      <ServiceAnswers
        serviceAnswers={serviceAnswers}
        selectedServiceAnswer={selectedServiceAnswer}
        serviceAnswerIDChoices={serviceAnswerIds}
        fetchServiceAnswers={this.fetchServiceAnswers}
        handleTrueFalseChange={this.handleTrueFalseChange}
        handleMinRangeAnswer={this.handleMinRangeAnswer}
        handleMaxRangeAnswer={this.handleMaxRangeAnswer}
        handleChoiceAnswer={this.handleChoiceAnswer}
        createServiceAnswer={this.createServiceAnswer}
        showServiceAnswerDetails={this.showServiceAnswerDetails}
        deleteServiceAnswer={this.deleteServiceAnswer}
        updateServiceAnswer={this.updateServiceAnswer}
        getServiceAnswerIDs={this.getServiceAnswerIDs}
        pageLeft={this.pageLeft}
        pageRight={this.pageRight}
      />
    );
  }
}
