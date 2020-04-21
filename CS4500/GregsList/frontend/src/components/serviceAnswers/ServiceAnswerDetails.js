import React from 'react';
import '../../styles/serviceQADetails.css';
class ServiceAnswerDetails extends React.Component {
  componentDidMount() {
    this.props.fetchServiceAnswer();
  }

  render() {
    return (
      <div>
        <h3>Service Answer Details</h3>
        <div className="service-q-a-details-whole-block">
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">ID</span>
            <select
              value={this.props.id}
              onChange={e => this.props.selectServiceAnswer(e.target.value)}
              className="form-control service-q-a-details-id-select"
            >
              {this.props.serviceAnswers.map(serviceAnswer => (
                <option value={serviceAnswer.id} key={serviceAnswer.id}>
                  {serviceAnswer.id}
                </option>
              ))}
            </select>
          </div>
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">True/False</span>
            <input
              onChange={this.props.handleTrueFalseChange}
              className="form-control service-q-a-details-field-input"
              value={this.props.serviceAnswer.trueFalseAnswer}
            />
          </div>
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">
              Min Range Answer
            </span>
            <input
              onChange={this.props.handleMinRangeAnswer}
              className="form-control service-q-a-details-field-input"
              value={this.props.serviceAnswer.minRangeAnswer}
            />
          </div>
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">
              Max Range Answer
            </span>
            <input
              onChange={this.props.handleMaxRangeAnswer}
              className="form-control service-q-a-details-field-input"
              value={this.props.serviceAnswer.maxRangeAnswer}
            />
          </div>
          <div className="service-q-a-details-field">
            <span className="service-q-a-details-field-header">
              Choice Answer
            </span>
            <input
              onChange={this.props.handleChoiceAnswer}
              className="form-control service-q-a-details-field-input"
              value={this.props.serviceAnswer.choiceAnswer}
            />
          </div>
          <div>
            <button
              className="service-q-a-details-button"
              onClick={this.props.backToAnswers}
            >
              Cancel
            </button>
            <button
              className="service-q-a-details-button"
              onClick={() =>
                this.props.deleteServiceAnswer(this.props.serviceAnswer.id)
              }
            >
              Delete
            </button>
            <button
              className="service-q-a-details-button"
              onClick={this.props.createServiceAnswer}
            >
              Create
            </button>
            <button
              className="service-q-a-details-button"
              onClick={this.props.updateServiceAnswer}
            >
              Update
            </button>
          </div>
        </div>
      </div>
    );
  }
}

export default ServiceAnswerDetails;
