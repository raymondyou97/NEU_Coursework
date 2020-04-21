import React from 'react';
import '../../styles/serviceQA.css';

class ServiceAnswers extends React.Component {
  componentDidMount() {
    this.props.fetchServiceAnswers();
  }

  render() {
    const {
      serviceAnswers,
      selectedServiceAnswer,
      serviceAnswerIDChoices,
      handleTrueFalseChange,
      handleMinRangeAnswer,
      handleMaxRangeAnswer,
      handleChoiceAnswer,
    } = this.props;

    return (
      <div className="service-answer-table">
        <h3>Service Answers</h3>
        <table className="service-q-a-table">
          <thead className="service-q-a-header">
            {/* This is the name of the columns */}
            <tr className="service-q-a-table-row">
              <th>ID</th>
              <th>True or False</th>
              <th>Min Range Answer</th>
              <th>Max Range Answer</th>
              <th>Choice Answer</th>
              <th>Commands</th>
            </tr>
          </thead>
          <tbody>
            {/* This is the input fields for the columns */}
            <tr className="service-q-a-input-row">
              <td>{serviceAnswerIDChoices}</td>
              <td>
                <input
                  type="text"
                  onChange={handleTrueFalseChange}
                  placeholder="t/f"
                  value={selectedServiceAnswer.trueFalseAnswer}
                  className="service-answer-input-true-false"
                />
              </td>
              <td>
                <input
                  type="number"
                  onChange={handleMinRangeAnswer}
                  placeholder="0"
                  value={selectedServiceAnswer.minRangeAnswer}
                  className="service-answer-input-min-range"
                />
              </td>
              <td>
                <input
                  type="number"
                  onChange={handleMaxRangeAnswer}
                  placeholder="0"
                  value={selectedServiceAnswer.maxRangeAnswer}
                  className="service-answer-input-max-range"
                />
              </td>
              <td>
                <input
                  type="number"
                  onChange={handleChoiceAnswer}
                  placeholder="0"
                  value={selectedServiceAnswer.choiceAnswer}
                  className="service-answer-input-choice"
                />
              </td>
              <td className="service-q-a-input-buttons">
                <button
                  className="service-q-a-add-button"
                  onClick={this.props.createServiceAnswer}
                >
                  Add
                </button>
                <button
                  className="service-q-a-update-button"
                  onClick={this.props.updateServiceAnswer}
                >
                  Update
                </button>
              </td>
            </tr>
            {serviceAnswers.map(serviceAnswer => {
              return (
                <tr key={serviceAnswer.id} className="service-q-a-table-row">
                  <td>{serviceAnswer.id}</td>
                  {serviceAnswer.trueFalseAnswer ? (
                    <td>{serviceAnswer.trueFalseAnswer.toString()}</td>
                  ) : (
                    <td>-</td>
                  )}
                  {serviceAnswer.minRangeAnswer ? (
                    <td>{serviceAnswer.minRangeAnswer}</td>
                  ) : (
                    <td>-</td>
                  )}
                  {serviceAnswer.maxRangeAnswer ? (
                    <td>{serviceAnswer.maxRangeAnswer}</td>
                  ) : (
                    <td>-</td>
                  )}
                  {serviceAnswer.choiceAnswer ? (
                    <td>{serviceAnswer.choiceAnswer}</td>
                  ) : (
                    <td>-</td>
                  )}
                  <td>
                    <button
                      className="service-q-a-show-button"
                      onClick={() =>
                        this.props.showServiceAnswerDetails(serviceAnswer.id)
                      }
                    >
                      Show
                    </button>
                    <button
                      className="service-q-a-delete-button"
                      onClick={() =>
                        this.props.deleteServiceAnswer(serviceAnswer.id)
                      }
                    >
                      Delete
                    </button>
                  </td>
                </tr>
              );
            })}
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

export default ServiceAnswers;
