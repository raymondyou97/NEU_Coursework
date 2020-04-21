import React, { PureComponent } from 'react';
import ServiceQuestionService from '../../services/ServiceQuestionService';
import ServiceQuestions from './ServiceQuestions';

class ServiceQuestionsContainer extends PureComponent {
  constructor(props) {
    super(props);
    this.serviceQuestionService = ServiceQuestionService.getInstance();
    this.state = {
      serviceQuestions: [],
      newQuestion: '',
      newType: '',
      newChoices: '',
      selectedQuestionId: -1,
      currentPage: 0,
      totalPages: 0,
      count: 10,
    };
  }

  fetchServiceQuestions = () => {
    this.serviceQuestionService
      .findPagedServiceQuestions(this.state.currentPage, this.state.count)
      .then(pagedQuestions => {
        if (pagedQuestions.content) {
          this.setState({
            serviceQuestions: pagedQuestions.content,
            totalPages: pagedQuestions.totalPages,
          });
        }
      });
  };

  handleQuestionChange = e => {
    this.setState({ newQuestion: e.target.value });
  };

  handleTypeChange = e => {
    this.setState({ newType: e.target.value });
  };

  handleChoicesChange = e => {
    this.setState({ newChoices: e.target.value });
  };

  handleIdChange = e => {
    if (e.target.value === '-1') {
      this.setState({
        newQuestion: '',
        newType: '',
        newChoices: '',
        selectedQuestionId: -1,
      });
    } else {
      let serviceQuestion = this.state.serviceQuestions.find(question => {
        return question.id.toString() === e.target.value;
      });
      this.setState({
        newQuestion: serviceQuestion.question,
        newType: serviceQuestion.type,
        newChoices: serviceQuestion.choices,
        selectedQuestionId: e.target.value,
      });
    }
  };

  handleCountChange = e => {
    let count = e.target.value;
    if (count === 'All') {
      this.serviceQuestionService
        .findAllServiceQuestions()
        .then(serviceQuestions =>
          this.setState({
            serviceQuestions: serviceQuestions,
            count: count,
            totalPages: 1,
            currentPage: 0,
          })
        );
    } else {
      this.serviceQuestionService
        .findPagedServiceQuestions(0, count)
        .then(pagedQuestions =>
          this.setState({
            serviceQuestions: pagedQuestions.content,
            count: count,
            totalPages: pagedQuestions.totalPages,
            currentPage: 0,
          })
        );
    }
  };

  createServiceQuestion = () => {
    this.serviceQuestionService
      .createServiceQuestion({
        question: this.state.newQuestion,
        type: this.state.newType,
        choices: this.state.newChoices,
      })
      .then(respData => {
        this.setState(prevState => ({
          serviceQuestions: prevState.serviceQuestions.concat(respData),
          newQuestion: '',
          newType: '',
          newChoices: '',
        }));
      });
  };

  deleteServiceQuestion = id => {
    this.serviceQuestionService.deleteServiceQuestion(id).then(response => {
      if (response.status === 200) {
        let newServiceQuestions = this.state.serviceQuestions.filter(
          question => {
            return question.id !== id;
          }
        );
        this.setState({
          serviceQuestions: newServiceQuestions,
        });
      } else {
        alert(`Failed to delete service question with id: ${id}`);
      }
    });
  };

  updateServiceQuestion = () => {
    if (this.state.selectedQuestionId !== -1) {
      let newServiceQuestion = {
        id: parseInt(this.state.selectedQuestionId),
        question: this.state.newQuestion,
        type: this.state.newType,
        choices: this.state.newChoices,
      };

      this.serviceQuestionService
        .updateServiceQuestion(
          this.state.selectedQuestionId,
          newServiceQuestion
        )
        .then(respData => {
          let newServiceQuestions = [];
          this.state.serviceQuestions.forEach(question => {
            if (question.id.toString() === this.state.selectedQuestionId) {
              newServiceQuestions.push(newServiceQuestion);
            } else {
              newServiceQuestions.push(question);
            }
          });
          this.setState({
            serviceQuestions: newServiceQuestions,
            newQuestion: '',
            newType: '',
            newChoices: '',
          });
        });
    } else {
      alert('Select a id first.');
    }
  };

  showServiceQuestionDetails = id => {
    this.props.history.push(`/admin/service-questions/${id}`);
  };

  pageLeft = () => {
    if (this.state.currentPage !== 0 && this.state.count !== 'All') {
      let currentPage = this.state.currentPage - 1;
      this.serviceQuestionService
        .findPagedServiceQuestions(currentPage, this.state.count)
        .then(pagedQuestions =>
          this.setState({
            serviceQuestions: pagedQuestions.content,
            totalPages: pagedQuestions.totalPages,
            currentPage: currentPage,
          })
        );
    }
  };

  pageRight = () => {
    if (
      this.state.currentPage < this.state.totalPages - 1 &&
      this.state.count !== 'All'
    ) {
      let currentPage = this.state.currentPage + 1;
      this.serviceQuestionService
        .findPagedServiceQuestions(currentPage, this.state.count)
        .then(pagedQuestions =>
          this.setState({
            serviceQuestions: pagedQuestions.content,
            totalPages: pagedQuestions.totalPages,
            currentPage: currentPage,
          })
        );
    }
  };

  getServiceQuestionIDs = () => {
    let serviceQuestionIDs = [];
    //option for when you want to add new row
    serviceQuestionIDs.push(<option key={-1} value={-1}></option>);
    for (let i = 0; i < this.state.serviceQuestions.length; i++) {
      serviceQuestionIDs.push(
        <option
          key={this.state.serviceQuestions[i].id}
          value={this.state.serviceQuestions[i].id}
        >
          {this.state.serviceQuestions[i].id}
        </option>
      );
    }
    let serviceQuestionIDChoices = (
      <select onChange={this.handleIdChange}>{serviceQuestionIDs}</select>
    );

    return serviceQuestionIDChoices;
  };

  render() {
    const { newQuestion, newType, newChoices } = this.state;

    const selectedServiceQuestion = {
      newQuestion,
      newType,
      newChoices,
    };

    const serviceQuestionIds = this.getServiceQuestionIDs();

    return (
      <ServiceQuestions
        serviceQuestions={this.state.serviceQuestions}
        selectedServiceQuestion={selectedServiceQuestion}
        serviceQuestionIDChoices={serviceQuestionIds}
        fetchServiceQuestions={this.fetchServiceQuestions}
        handleQuestionChange={this.handleQuestionChange}
        handleTypeChange={this.handleTypeChange}
        handleChoicesChange={this.handleChoicesChange}
        handleCountChange={this.handleCountChange}
        createServiceQuestion={this.createServiceQuestion}
        showServiceQuestionDetails={this.showServiceQuestionDetails}
        deleteServiceQuestion={this.deleteServiceQuestion}
        updateServiceQuestion={this.updateServiceQuestion}
        getServiceQuestionIDs={this.getServiceQuestionIDs}
        pageLeft={this.pageLeft}
        pageRight={this.pageRight}
      />
    );
  }
}

export default ServiceQuestionsContainer;
