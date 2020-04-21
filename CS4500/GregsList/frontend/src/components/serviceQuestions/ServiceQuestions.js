import React from 'react';
import '../../styles/serviceQA.css';

class ServiceQuestions extends React.Component {
  componentDidMount() {
    this.props.fetchServiceQuestions();
  }

  handleQuestionChange = e => {
    this.props.handleQuestionChange(e);
  };

  handleTypeChange = e => {
    this.props.handleTypeChange(e);
  };

  handleChoicesChange = e => {
    this.props.handleChoicesChange(e);
  };

  deleteServiceQuestion = id => {
    this.props.deleteServiceQuestion(id);
  };

  render() {
    let { selectedServiceQuestion, serviceQuestionIDChoices } = this.props;

    return (
      <div className="service-question-table">
        <h3>Service Questions</h3>
        <div>
          Note: Types are (TrueFalse, MultipleChoice, Range) and choices are
          Comma-separated
        </div>
        <table className="service-q-a-table">
          <thead className="service-q-a-table-header">
            <tr className="service-q-a-table-row">
              <th>ID</th>
              <th>Question</th>
              <th>Type</th>
              <th>Choices</th>
              <th>Commands</th>
            </tr>
          </thead>
          <tbody className="service-q-a-tableBody">
            <tr className="service-q-a-input-row">
              <td>{serviceQuestionIDChoices}</td>
              <td>
                <input
                  type="text"
                  placeholder="Question"
                  value={selectedServiceQuestion.newQuestion}
                  className="service-question-input-question"
                  onChange={this.handleQuestionChange}
                />
              </td>
              <td>
                <input
                  type="text"
                  placeholder="Type"
                  value={selectedServiceQuestion.newType}
                  className="service-question-input-type"
                  onChange={this.handleTypeChange}
                />
              </td>
              <td>
                <input
                  type="text"
                  placeholder="Choices"
                  value={selectedServiceQuestion.newChoices}
                  className="service-question-input-choices"
                  onChange={this.handleChoicesChange}
                />
              </td>
              <td>
                <button
                  className="service-q-a-add-button"
                  onClick={() => this.props.createServiceQuestion()}
                >
                  Add
                </button>
                <button
                  className="service-q-a-update-button"
                  onClick={() => this.props.updateServiceQuestion()}
                >
                  Update
                </button>
              </td>
            </tr>
            {this.props.serviceQuestions.map(serviceQuestion => (
              <tr key={serviceQuestion.id} className="service-q-a-table-row">
                <td>{serviceQuestion.id}</td>
                <td>{serviceQuestion.question}</td>
                <td>{serviceQuestion.type}</td>
                <td>{serviceQuestion.choices}</td>
                <td>
                  <button
                    className="service-q-a-show-button"
                    onClick={() =>
                      this.props.showServiceQuestionDetails(serviceQuestion.id)
                    }
                  >
                    Show
                  </button>
                  <button
                    className="service-q-a-delete-button"
                    onClick={() =>
                      this.props.deleteServiceQuestion(serviceQuestion.id)
                    }
                  >
                    Delete
                  </button>
                </td>
              </tr>
            ))}
          </tbody>
        </table>
        <div className="pagination-row">
          <select onChange={this.props.handleCountChange}>
            <option value={10}>10</option>
            <option value={25}>25</option>
            <option value={50}>50</option>
            <option value={100}>100</option>
            <option value={'All'}>All</option>
          </select>
          <button className="pagination-button" onClick={this.props.pageLeft}>
            Prev
          </button>
          <button className="pagination-button" onClick={this.props.pageRight}>
            Next
          </button>
        </div>
      </div>
    );
  }
}

export default ServiceQuestions;
