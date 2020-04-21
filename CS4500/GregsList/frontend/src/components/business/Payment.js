import React from 'react';
import '../../styles/business.css';

class BusinessPayment extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      selectedCheckboxes: new Set(),
    };
    this.validPaymentOptions = [
      'Credit Card',
      'Cash',
      'Check',
      'Venmo',
      'Paypal',
      'Square',
    ];
  }

  componentDidMount() {
    this.setState({ selectedCheckboxes: new Set() });
  }

  toggleCheckbox(choice) {
    let selected = this.state.selectedCheckboxes;
    if (selected.has(choice)) {
      selected.delete(choice);
    } else {
      selected.add(choice);
    }
    this.setState({ selectedCheckboxes: selected });
    this.props.paymentOptions(selected);
  }

  getPaymentOptions() {
    let initialChecked = [];
    if (
      this.props.initialState &&
      this.props.initialState.businessPaymentMethods
    ) {
      initialChecked = this.props.initialState.businessPaymentMethods.split(
        ','
      );
    }

    return this.validPaymentOptions.map((choice, index) => (
      <div className="row justify-content-md-center" key={index}>
        <div className="col-12">
          <label>
            <input
              name="Payment Options"
              type="checkbox"
              value={choice}
              onChange={() => this.toggleCheckbox(choice)}
              checked={initialChecked.includes(choice) ? true : false}
            />
            <span>&nbsp;{choice}</span>
          </label>
        </div>
      </div>
    ));
  }

  render() {
    return (
      <div>
        <h5>Payment Methods Accepted</h5>
        {this.getPaymentOptions()}
      </div>
    );
  }
}

export default BusinessPayment;
