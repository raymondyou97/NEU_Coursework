import React, { Component } from 'react';

import '../../styles/services/services.css';

class Services extends Component {
  componentDidMount() {
    this.props.findAllServices();
  }

  deleteService = id => {
    this.props.deleteService(id);
  };

  enableEdits = (id, title) => {
    this.props.enableEdits(id, title);
  };

  handleTitleChange = e => {
    this.props.handleTitleChange(e.target.value);
  };

  showService = id => {
    this.props.showService(id);
  };

  render() {
    const { newTitle } = this.props;
    return (
      <div>
        <h3>Services</h3>
        <table className="service-table">
          <tbody className="service-table-body">
            <tr className="service-columns">
              <td>Title</td>
            </tr>
            <tr className="service-inputs">
              <td>
                <input
                  className="service-input-title"
                  type="text"
                  placeholder="Title"
                  value={newTitle}
                  onChange={this.handleTitleChange}
                />
              </td>
              <td className="service-input-buttons">
                <button
                  className="service-add-button"
                  onClick={() => this.props.createService()}
                >
                  Add
                </button>
                <button
                  className="service-update-button"
                  onClick={() => this.props.updateService()}
                >
                  Update
                </button>
              </td>
            </tr>
            {this.props.services.map(service => (
              <tr className="service-details" key={service.id}>
                <td onClick={() => this.showService(service.id)}>
                  {service.title}
                </td>
                <td className="service-buttons">
                  <button
                    className="service-delete-button"
                    onClick={() => this.deleteService(service.id)}
                  >
                    Delete
                  </button>
                  <button
                    className="service-edit-button"
                    onClick={() => this.enableEdits(service.id, service.title)}
                  >
                    Edit
                  </button>
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    );
  }
}

export default Services;
