import React from 'react';
import '../../styles/business.css';

class BusinessSocial extends React.Component {
  constructor(props) {
    super(props);
    this.state = {};
  }

  updateFacebook(e) {
    let newFacebook = e.target.value;
    this.props.facebookURL(newFacebook);
  }

  updateInstagram(e) {
    let newInstagram = e.target.value;
    this.props.instagramURL(newInstagram);
  }

  updateTwitter(e) {
    let newTwitter = e.target.value;
    this.props.twitterURL(newTwitter);
  }

  render() {
    let initialState = this.props.initialState;
    return (
      <div>
        <h5>Social Media</h5>
        <div className="row">
          <div className="col-12">
            <label htmlFor="facebookInput">Facebook URL</label>
            <input
              type="text"
              className="form-control"
              id="facebookInput"
              value={initialState.businessFacebookURL}
              onChange={e => this.updateFacebook(e)}
            />
          </div>
        </div>
        <div className="row">
          <div className="col-12">
            <label htmlFor="instagramInput">Instagram URL</label>
            <input
              type="text"
              className="form-control"
              id="instagramInput"
              value={initialState.businessInstagramURL}
              onChange={e => this.updateInstagram(e)}
            />
          </div>
        </div>
        <div className="row">
          <div className="col-12">
            <label htmlFor="twitterInput">Twitter URL</label>
            <input
              type="text"
              className="form-control"
              id="twitterInput"
              value={initialState.businessTwitterURL}
              onChange={e => this.updateTwitter(e)}
            />
          </div>
        </div>
      </div>
    );
  }
}

export default BusinessSocial;
