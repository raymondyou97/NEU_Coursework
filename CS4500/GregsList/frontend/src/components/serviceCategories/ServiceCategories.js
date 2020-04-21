import React from 'react';

import '../../styles/serviceCategories.css';

class ServiceCategories extends React.Component {
  componentDidMount() {
    this.props.fetchServiceCategories();
  }

  updateTitle = e => {
    this.props.updateTitle(e.target.value);
  };

  updateDescription = e => {
    this.props.updateDescription(e.target.value);
  };

  deleteServiceCategory = id => {
    this.props.deleteServiceCategory(id);
  };

  editServiceCategory = (id, title, description) => {
    this.props.updateId(id);
    this.props.updateTitle(title);
    this.props.updateDescription(description);
  };

  render() {
    const { serviceCategory } = this.props;

    return (
      <div>
        <h3 className="service-category-title">Service Categories</h3>
        <table className="service-category-table">
          <tbody className="service-category-table-body">
            <tr className="service-category-columns">
              <td>Title</td>
              <td>Description</td>
              <td></td>
            </tr>
            <tr className="service-category-inputs">
              <td>
                <input
                  className="service-category-title-input"
                  type="text"
                  placeholder="Title"
                  value={serviceCategory.title}
                  onChange={this.updateTitle}
                />
              </td>
              <td>
                <input
                  className="service-category-description-input"
                  type="text"
                  placeholder="Description"
                  value={serviceCategory.description}
                  onChange={this.updateDescription}
                />
              </td>
              <td className="service-category-input-buttons">
                <button
                  className="service-category-add-button"
                  onClick={this.props.createServiceCategory}
                >
                  Add
                </button>
                <button
                  className="service-category-update-button"
                  onClick={this.props.updateServiceCategory}
                >
                  Update
                </button>
              </td>
            </tr>
            {this.props.serviceCategories.map(serviceCategory => {
              const { id, title, description } = serviceCategory;
              return (
                <tr className="service-category-details" key={id}>
                  <td onClick={() => this.props.showDetails(id)}>{title}</td>
                  <td onClick={() => this.props.showDetails(id)}>
                    {description}
                  </td>
                  <td className="service-category-buttons">
                    <button
                      className="service-category-delete-button"
                      onClick={() => this.deleteServiceCategory(id)}
                    >
                      Delete
                    </button>
                    <button
                      className="service-category-edit-button"
                      onClick={() =>
                        this.editServiceCategory(id, title, description)
                      }
                    >
                      Edit
                    </button>
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>
    );
  }
}

export default ServiceCategories;
