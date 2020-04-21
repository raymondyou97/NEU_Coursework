import React from 'react';
import ServiceQuestionService from '../../services/ServiceQuestionService';
import '../../styles/serviceQADetails.css';

class ServiceQuestionDetails extends React.Component {
  constructor(props) {
    super(props);
    this.serviceQuestionService = ServiceQuestionService.getInstance();
    this.state = {
      id: this.props.match.params.id,
      serviceQuestions: [],
      serviceQuestion: {
        id: 0,
        question: '',
        type: '',
        choices: '',
      },
    };
  }

  componentDidMount() {
    this.serviceQuestionService
      .findAllServiceQuestions()
      .then(serviceQuestions => {
        //this.props.history.push("/admin/service-questions/" + serviceQuestions[0].id)
        this.setState({
          serviceQuestions: serviceQuestions,
          //serviceQuestion: serviceQuestions[0]
        });
      });
    this.selectServiceQuestion(this.state.id);
  }

  selectServiceQuestion = id => {
    this.serviceQuestionService
      .findServiceQuestionById(id)
      .then(serviceQuestion => {
        console.log(serviceQuestion);
        this.props.history.push('/admin/service-questions/' + id);
        this.setState({
          serviceQuestion: serviceQuestion,
        });
      });
  };

  render() {
    return (
      <div>
        <h3>Service Question Details</h3>
        <div className="service-q-a-details-whole-block">
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">ID</span>
            <select
              value={this.state.serviceQuestion.id}
              onChange={e => this.selectServiceQuestion(e.target.value)}
              className="form-control service-q-a-details-field-input"
            >
              {this.state.serviceQuestions.map(serviceQuestion => (
                <option value={serviceQuestion.id} key={serviceQuestion.id}>
                  {serviceQuestion.id}
                </option>
              ))}
            </select>
          </div>
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">Question</span>
            <input
              onChange={() => {}}
              className="form-control service-q-a-details-field-input"
              value={this.state.serviceQuestion.question}
            />
          </div>
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">Type</span>
            <input
              onChange={() => {}}
              className="form-control service-q-a-details-field-input"
              value={this.state.serviceQuestion.type}
            />
          </div>
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">Choices</span>
            <input
              onChange={() => {}}
              className="form-control service-q-a-details-field-input"
              value={this.state.serviceQuestion.choices}
            />
          </div>
          <div>
            <button className="service-q-a-details-button">Cancel</button>
            <button className="service-q-a-details-button">Delete</button>
            <button className="service-q-a-details-button">Create</button>
            <button className="service-q-a-details-button">Update</button>
          </div>
        </div>
      </div>
    );
  }
}

export default ServiceQuestionDetails;
