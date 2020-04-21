import React from 'react';
import '../../styles/business.css';

class BusinessAddress extends React.Component {
  updateState(e) {
    let newState = e.target.value;
    this.props.state(newState);
  }

  updateStreet(e) {
    let newStreet = e.target.value;
    this.props.street(newStreet);
  }

  updateCity(e) {
    let newCity = e.target.value;
    this.props.city(newCity);
  }

  updateZip(e) {
    let newZip = e.target.value;
    this.props.zip(newZip);
  }

  getStates(initialState) {
    return (
      <div className="col-6">
        <label for="businessStateInput">State</label>
        <select
          className="form-control"
          id="businessStateInput"
          value={initialState}
          onChange={e => this.updateState(e)}
        >
          <option>N/A</option>
          <option value="AL">Alabama</option>
          <option value="AK">Alaska</option>
          <option value="AZ">Arizona</option>
          <option value="AR">Arkansas</option>
          <option value="CA">California</option>
          <option value="CO">Colorado</option>
          <option value="CT">Connecticut</option>
          <option value="DE">Delaware</option>
          <option value="DC">District Of Columbia</option>
          <option value="FL">Florida</option>
          <option value="GA">Georgia</option>
          <option value="HI">Hawaii</option>
          <option value="ID">Idaho</option>
          <option value="IL">Illinois</option>
          <option value="IN">Indiana</option>
          <option value="IA">Iowa</option>
          <option value="KS">Kansas</option>
          <option value="KY">Kentucky</option>
          <option value="LA">Louisiana</option>
          <option value="ME">Maine</option>
          <option value="MD">Maryland</option>
          <option value="MA">Massachusetts</option>
          <option value="MI">Michigan</option>
          <option value="MN">Minnesota</option>
          <option value="MS">Mississippi</option>
          <option value="MO">Missouri</option>
          <option value="MT">Montana</option>
          <option value="NE">Nebraska</option>
          <option value="NV">Nevada</option>
          <option value="NH">New Hampshire</option>
          <option value="NJ">New Jersey</option>
          <option value="NM">New Mexico</option>
          <option value="NY">New York</option>
          <option value="NC">North Carolina</option>
          <option value="ND">North Dakota</option>
          <option value="OH">Ohio</option>
          <option value="OK">Oklahoma</option>
          <option value="OR">Oregon</option>
          <option value="PA">Pennsylvania</option>
          <option value="RI">Rhode Island</option>
          <option value="SC">South Carolina</option>
          <option value="SD">South Dakota</option>
          <option value="TN">Tennessee</option>
          <option value="TX">Texas</option>
          <option value="UT">Utah</option>
          <option value="VT">Vermont</option>
          <option value="VA">Virginia</option>
          <option value="WA">Washington</option>
          <option value="WV">West Virginia</option>
          <option value="WI">Wisconsin</option>
          <option value="WY">Wyoming</option>
        </select>
      </div>
    );
  }

  render() {
    let initialState = this.props.initialState;
    return (
      <div>
        <h5>Business Address (optional)</h5>
        <div className="row">
          <div className="col-12">
            <label htmlFor="businessStreetInput">Street</label>
            <input
              type="text"
              className="form-control"
              id="businessStreetInput"
              value={initialState.businessAddressStreet}
              onChange={e => this.updateStreet(e)}
            ></input>
          </div>
        </div>
        <div className="row">
          <div className="col-12">
            <label htmlFor="businessCityInput">City</label>
            <input
              type="text"
              className="form-control"
              id="businessCityInput"
              value={initialState.businessAddressCity}
              onChange={e => this.updateCity(e)}
            ></input>
          </div>
        </div>
        <div className="row">
          {this.getStates(initialState.businessAddressState)}
          <div className="col-6">
            <label htmlFor="businessZipInput">Zip</label>
            <input
              type="text"
              className="form-control"
              id="businessZipInput"
              value={initialState.businessAddressZip}
              onChange={e => this.updateZip(e)}
            ></input>
          </div>
        </div>
      </div>
    );
  }
}

export default BusinessAddress;
