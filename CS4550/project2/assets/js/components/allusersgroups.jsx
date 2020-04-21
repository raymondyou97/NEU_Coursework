import React from 'react';
import _ from 'lodash';
import api from '../utils/api';

class AllUsersGroups extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            usersgroups: []
        };
    }

    componentDidMount() {
        this.getUsersGroups();
    }

    getUsersGroups() {
        api.getRequest('api/v1/usersgroups', (resp) => {
            this.setState({
                usersgroups: resp.data
            });
        });
    }

    render() {
        return (
            <div>
                <h5>All UsersGroups</h5>
                <table className="table table-bordered table-hover">
                    <thead className="thead-dark">
                        <tr>
                            <th>id</th>
                            <th>group_id</th>
                            <th>user_id</th>
                        </tr>
                    </thead>
                    <tbody>
                        {this.state.usersgroups.map(usersgroup =>
                            <tr key={usersgroup.id}>
                                <td>{usersgroup.id}</td>
                                <td>{usersgroup.group_id}</td>
                                <td>{usersgroup.user_id}</td>
                            </tr>
                        )}
                    </tbody>
                </table>
            </div>
        )
    }
}

export default AllUsersGroups;