import React from 'react';
import _ from 'lodash';
import api from '../utils/api';
import cookie_helper from '../utils/cookie_helper';
import FileBase64 from 'react-file-base64';

class MyProfile extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            id: null,
            admin: false,
            email: "",
            age: null,
            fname: "",
            lname: "",
            gender: "",
            profile_url: "",
            base64_image_url: ""
        };
    }

    componentDidMount() {
        let user_session = cookie_helper.getUserSession();
        if (user_session) {
            let user_id = user_session.user_id;
            this.getUserProfileData(user_id);
        }
    }

    getUserProfileData(id) {
        api.getRequest(`api/v1/users/${id}`, (resp) => {
            this.setState(resp.data);
        });
    }

    getFile(file) {
        this.setState({
            base64_image_url: file.base64
        });
    }

    updateProPic() {
        if (this.state.base64_image_url.includes("data:image")) {
            let image = {
                "image": this.state.base64_image_url
            };
            $("#file-upload-modal").modal('show');
            api.postRequest("/api/v1/images", image, (resp) => {
                let imageUrl = resp.image_url;
                let newObj = {
                    user: {
                        profile_url: imageUrl
                    }
                };
                api.patchRequest(`api/v1/users/${this.state.id}`, newObj, (resp) => {
                    $("#file-upload-modal").modal('hide');
                    location.reload();
                });
            });
        }
        else {
            alert("File format is not an image");
        }
    }

    displayWaitingModal() {
        return (
            <div className="modal fade" id="file-upload-modal" tabIndex="-1" role="dialog">
                <div className="modal-dialog modal-dialog-centered" role="document">
                    <div className="modal-content">
                        <div className="modal-header">
                            <h3>Waiting for file to finish uploading...</h3>
                        </div>
                    </div>
                </div>
            </div>
        )
    }

    getProfileImage() {
        if (this.state.profile_url) {
            return <img className="card-img-top" src={this.state.profile_url} alt="base-profile-picture"></img>;
        }
        else {
            return <img className="card-img-top" src="/images/default-profile.png" alt="base-profile-picture"></img>;
        }
    }

    render() {
        return (
            <div className="card profile-card" style={{ width: '16.5rem' }}>
                {this.getProfileImage()}
                <div className="card-body">
                    <h5 className="card-title">My Profile</h5>
                    <ul className="list-group">
                        <li className="list-group-item">
                            <span className="bold-text">ID: </span>
                            {this.state.id}
                        </li>
                        <li className="list-group-item">
                            <span className="bold-text">Email: </span>
                            {this.state.email}
                        </li>
                        <li className="list-group-item">
                            <span className="bold-text">Admin: </span>
                            {this.state.admin.toString()}
                        </li>
                        <li className="list-group-item">
                            <span className="bold-text">Name: </span>
                            {this.state.fname} {this.state.lname}
                        </li>
                        <li className="list-group-item">
                            <span className="bold-text">Age: </span>
                            {this.state.age}
                        </li>
                        <li className="list-group-item">
                            <span className="bold-text">Gender: </span>
                            {this.state.gender}
                        </li>
                    </ul>
                </div>
                <FileBase64 multiple={false} onDone={(file) => this.getFile(file)} />
                {this.state.base64_image_url &&
                    <div className="upload-btn">
                        <button className="btn btn-primary" onClick={() => this.updateProPic()}>Update Profile Picture</button>
                    </div>
                }
                {this.displayWaitingModal()}
            </div>
        )
    }
}

export default MyProfile;