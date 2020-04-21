import React from 'react';
import _ from 'lodash';
import api from '../utils/api';

class AllUsers extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            users: []
        };
    }

    componentDidMount() {
        this.getUsers();
    }

    getUsers() {
        api.getRequest('api/v1/users', (resp) => {
            this.setState({
                users: resp.data
            });
        });
    }

    render() {
        return (
            <div>
                <h5>All Users</h5>
                <table className="table table-bordered table-hover">
                    <thead className="thead-dark">
                        <tr>
                            <th>id</th>
                            <th>email</th>
                            <th>fname</th>
                            <th>lname</th>
                            <th>gender</th>
                            <th>age</th>
                            <th>admin</th>
                        </tr>
                    </thead>
                    <tbody>
                        {this.state.users.map(user =>
                            <tr key={user.id}>
                                <td>{user.id}</td>
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
}

export default AllUsers;