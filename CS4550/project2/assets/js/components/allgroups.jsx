import React from 'react';
import _ from 'lodash';
import api from '../utils/api';

class AllGroups extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            groups: []
        };
    }

    componentDidMount() {
        this.getGroups();
    }

    getGroups() {
        api.getRequest('api/v1/groups', (resp) => {
            this.setState({
                groups: resp.data
            });
        });
    }

    render() {
        return (
            <div>
                <h5>All Groups</h5>
                <table className="table table-bordered table-hover">
                    <thead className="thead-dark">
                        <tr>
                            <th>id</th>
                            <th>name</th>
                            <th>description</th>
                        </tr>
                    </thead>
                    <tbody>
                        {this.state.groups.map(group =>
                            <tr key={group.id}>
                                <td>{group.id}</td>
                                <td>{group.name}</td>
                                <td>{group.desc}</td>
                            </tr>
                        )}
                    </tbody>
                </table>
            </div>
        )
    }
}

export default AllGroups;