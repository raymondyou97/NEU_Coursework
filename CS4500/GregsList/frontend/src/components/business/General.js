import React from 'react';
import '../../styles/business.css';

class BusinessGeneral extends React.Component {
  updateBusinessName(e) {
    let newBusinessName = e.target.value;
    this.props.businessName(newBusinessName);
  }

  updateYearFounded(e) {
    let newYearFounded = e.target.value;
    this.props.yearFounded(newYearFounded);
  }

  updateNumEmployees(e) {
    let newNumEmployees = e.target.value;
    this.props.numEmployees(newNumEmployees);
  }

  updateEmail(e) {
    let newEmail = e.target.value;
    this.props.email(newEmail);
  }

  render() {
    let initialState = this.props.initialState;
    return (
      <div>
        <h5>Business General</h5>
        <div className="row">
          <div className="col-12">
            <label htmlFor="businessNameInput">Business name</label>
            <input
              type="text"
              className="form-control"
              id="businessNameInput"
              value={initialState.title}
              onChange={e => this.updateBusinessName(e)}
            ></input>
          </div>
        </div>
        <div className="row">
          <div className="col-12">
            <label htmlFor="businessYearFoundedInput">Year founded</label>
            <input
              type="number"
              className="form-control"
              id="businessYearFoundedInput"
              value={initialState.businessYearFounded}
              onChange={e => this.updateYearFounded(e)}
            ></input>
          </div>
        </div>
        <div className="row">
          <div className="col-12">
            <label htmlFor="businessNumEmployeesInput">
              Number of employees
            </label>
            <input
              type="number"
              className="form-control"
              id="businessNumEmployeesInput"
              value={initialState.employees}
              onChange={e => this.updateNumEmployees(e)}
            ></input>
          </div>
        </div>
        <div className="row">
          <div className="col-12">
            <label htmlFor="businessEmailInput">Email</label>
            <input
              type="email"
              className="form-control"
              id="businessEmailInput"
              value={initialState.businessEmail}
              onChange={e => this.updateEmail(e)}
            ></input>
          </div>
        </div>
      </div>
    );
  }
}

export default BusinessGeneral;
