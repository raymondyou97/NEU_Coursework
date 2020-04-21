import React from 'react';
import { connect } from 'react-redux';

function UserList(props) {
    let rows = _.map(props.users, (user) => <User key={user.id} user={user} />);
    return <div className="container">
                <table className="table">
                    <thead className="thead-dark">
                        <tr>
                            <th>User ID</th>
                            <th>Email</th>
                        </tr>
                    </thead>
                    <tbody>
                        {rows}
                    </tbody>
                </table>
            </div>;
}

function User(props) {
    let {user} = props;
    return  <tr>
                <td>{user.id}</td>
                <td>{user.email}</td>
            </tr>;
}

export default connect((state) => {return {users: state.users};})(UserList);