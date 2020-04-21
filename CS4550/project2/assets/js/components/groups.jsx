import React from 'react';
import _ from 'lodash';
import api from '../utils/api';
import cookie_helper from '../utils/cookie_helper';

class Groups extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            allGroups: [],
            allUserGroups: [],
            user_id: -1,
            //modal stuff
            current_group_name: "",
            current_group_desc: "",
            current_group_members: []
        };
    }

    componentDidMount() {
        this.getUserData();
        this.getAllGroups();
    }

    getUserData() {
        let user_session = cookie_helper.getUserSession();
        if (user_session) {
            this.setState({
                user_id: user_session.user_id
            });
        }
    }

    getAllGroups() {
        api.getRequest('api/v1/groups', (groups) => {
            api.getRequest('api/v1/usersgroups', (usersgroups) => {
                this.setState({
                    allGroups: groups.data,
                    allUserGroups: usersgroups.data
                });
                this.getGroupView();
            })
        });
    }

    leaveGroup(group_id) {
        let usersgroup = this.state.allUserGroups.find(group => {
            return group.group_id == group_id;
        });
        alert(`Are you sure you want to leave group (${usersgroup.group_name})?`)
        api.deleteRequest('api/v1/usersgroups/', usersgroup.id, () => {
            this.getAllGroups();
            location.reload();
        });
    }

    joinGroup(group_id) {
        let newUsersgroup = {
            users_group: {
                user_id: this.state.user_id,
                group_id: group_id
            }
        };
        api.postRequest('api/v1/usersgroups', newUsersgroup, () => {
            alert("Successfully joined!");
            this.getAllGroups();
            location.reload()
        });
    }

    viewDetails(group_id) {
        //clear array first
        this.setState({ current_group_members: [] });

        let currentGroup = this.state.allGroups.find(group => group.id === group_id);
        let currentUserIdsInGroup = this.state.allUserGroups.filter(userGroup => {
            return userGroup.group_id === group_id;
        }).map(userGroup => userGroup.user_id);

        for (let i = 0; i < currentUserIdsInGroup.length; i++) {
            api.getRequest(`api/v1/users/${currentUserIdsInGroup[i]}`, (user) => {
                let newState = this.state.current_group_members.concat(user.data);
                this.setState({
                    current_group_members: newState
                });
            })
        }

        this.setState({
            current_group_name: currentGroup.name,
            current_group_desc: currentGroup.desc
        });
        $('#groupInfoModal').modal('toggle')
    }

    userIsGroupOwner(group_owner) {
        return group_owner == this.state.user_id;
    }

    getGroupView() {
        let myGroupIds = this.state.allUserGroups.filter(group => {
            return group.user_id === this.state.user_id
        }).map(group => group.group_id);

        let view = this.state.allGroups.map(group => {
            if (myGroupIds.includes(group.id)) {
                return (
                    <tr key={group.id}>
                        <td>{group.id}</td>
                        <td>{group.name}</td>
                        <td>{group.desc}</td>
                        <td>
                            <button className="btn btn-danger" onClick={() => this.leaveGroup(group.id)}>Leave</button>
                            <button className="btn btn-info" onClick={() => this.viewDetails(group.id)}>View Details</button>
                            {this.userIsGroupOwner(group.owner_id) && <button className="btn btn-danger" onClick={() => this.deleteGroup(group.owner_id)}>Delete Group</button>}
                        </td>
                    </tr>
                )
            } else {
                return (
                    <tr key={group.id}>
                        <td>{group.id}</td>
                        <td>{group.name}</td>
                        <td>{group.desc}</td>
                        <td>
                            <button className="btn btn-success" onClick={() => this.joinGroup(group.id)}>Join</button>
                            <button className="btn btn-info" onClick={() => this.viewDetails(group.id)}>View Details</button>
                            {this.userIsGroupOwner(group.owner_id) && <button className="btn btn-danger" onClick={() => this.deleteGroup(group.owner_id)}>Delete Group</button>}
                        </td>
                    </tr>
                )
            }
        });
        return view;
    }

    groupInfoModalMembers() {
        if (this.state.current_group_members.length > 0) {
            return (
                <div>
                    <span className="group-column">Current Group Members:</span>
                    <table className="table table-bordered table-hover">
                        <thead className="thead-dark">
                            <tr>
                                <th>email</th>
                                <th>fname</th>
                                <th>lname</th>
                                <th>gender</th>
                                <th>age</th>
                                <th>admin</th>
                            </tr>
                        </thead>
                        <tbody>
                            {this.state.current_group_members.map(user =>
                                <tr key={user.id}>
                                    <td>{user.email}</td>
                                    <td>{user.fname}</td>
                                    <td>{user.lname}</td>
                                    <td>{user.gender}</td>
                                    <td>{user.age}</td>
                                    <td>{user.admin.toString()}</td>
                                </tr>
                            )}
                        </tbody>
                    </table>
                </div>
            )
        }
        else {
            return <span> 0</span>
        }
    }

    createGroup() {
        let name = document.getElementById("name-input").value;
        let desc = document.getElementById("desc-input").value;
        let newGroup = {
            group: {
                name: name,
                desc: desc,
                owner_id: this.state.user_id
            }
        };
        if (this.createGroupInputFormChecker(newGroup.group)) {
            api.postRequest("/api/v1/groups", newGroup, () => {
                alert("New group successfully created!");
                $("#name-input").val('');
                $("#desc-input").val('');
                this.getAllGroups();
                location.reload();
            });
        }
    }

    createGroupInputFormChecker(group) {
        if (group) {
            if (group.name == "" || !group.name) {
                alert("Please enter a name for the group.");
                return false;
            }
            else if (group.desc === "") {
                alert("Please enter a description for the group.");
                return false;
            }
        }
        return true;
    }

    displayAddGroupModal() {
        return (
            <div className="modal fade" id="createGroupModal" tabIndex="-1" role="dialog">
                <div className="modal-dialog modal-dialog-centered" role="document">
                    <div className="modal-content">
                        <div className="modal-header">
                            <h3>Create a new group</h3>
                        </div>
                        <div className="modal-body">
                            <div className="register-container">
                                <div className="input-group mb-3">
                                    <input type="text" className="form-control" id="name-input" placeholder="Group name"></input>
                                </div>
                                <div className="input-group mb-3">
                                    <input type="text" className="form-control" id="desc-input" placeholder="Description"></input>
                                </div>
                            </div>
                        </div>
                        <div className="modal-footer">
                            <button className="btn btn-success" onClick={() => this.createGroup()}>Create Group</button>
                            <button id="close-register-modal-btn" type="button" className="btn btn-secondary" data-dismiss="modal">Close</button>
                        </div>
                    </div>
                </div>
            </div>
        )
    }

    deleteGroup(id) {
        alert("Are you sure you want to delete this group?");
        api.deleteRequest('api/v1/groups/', id, (resp) => {
            let filteredGroups = this.state.allGroups.filter(group => {
                return group.id !== id
            });
            this.setState({
                allGroups: filteredGroups
            });
        })
    }

    groupInfoModal() {
        return (
            <div className="modal fade" id="groupInfoModal" tabIndex="-1" role="dialog">
                <div className="modal-dialog modal-dialog-centered modal-lg" role="document">
                    <div className="modal-content">
                        <div className="modal-header">
                            <h3>{this.state.current_group_name}</h3>
                        </div>
                        <div className="modal-body">
                            <div>
                                <span className="group-column">Description: </span>
                                {this.state.current_group_desc}
                            </div>
                            <div className="tab-content">
                                <div>
                                    {this.state.current_group_members.length === 0 && <span className="group-column">Current Group Members:</span>}
                                    {this.groupInfoModalMembers()}
                                </div>
                            </div>
                        </div>
                        <div className="modal-footer">
                            <button type="button" className="btn btn-secondary" data-dismiss="modal">Close</button>
                        </div>
                    </div>
                </div>
            </div>
        )
    }

    render() {
        return (
            <div>
                <h5>All Groups</h5>
                <button className="btn btn-secondary" data-toggle="modal" data-target="#createGroupModal">Create New Group</button>
                <table className="table table-bordered table-hover">
                    <thead className="thead-dark">
                        <tr>
                            <th>id</th>
                            <th>name</th>
                            <th>description</th>
                            <th>options</th>
                        </tr>
                    </thead>
                    <tbody>
                        {this.getGroupView()}
                    </tbody>
                </table>
                {this.groupInfoModal()}
                {this.displayAddGroupModal()}
            </div>
        )
    }
}

export default Groups;
