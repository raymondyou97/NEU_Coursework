import React from 'react';
import _ from 'lodash';
import api from '../utils/api';

class Group extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            group: []
        };
    }

    componentDidMount() {
      this.getGroup();
    }


    getGroup() {
      api.getRequest('/api/v1/groups/' + this.props.match.params.id, (resp) => {
          this.setState({
              group: resp.data
          });
      });
    }

    render() {
        return (
            <div>
                <h2>{this.state.group.name}</h2>
                <h5>{this.state.group.desc}</h5>
                <br/>
                <h5>Foodies</h5>
                <table className="table table-bordered table-hover">
                    <thead className="thead-dark">
                        <tr>
                            <th>name</th>
                            <th>name</th>
                            <th>description</th>
                        </tr>
                    </thead>
                    <tbody>
                    <tr>
                        <td>{this.state.group.id}</td>
                        <td>{this.state.group.name}</td>
                        <td>{this.state.group.desc}</td>
                    </tr>

                    </tbody>
                </table>
                <h5>Recipes</h5>
            </div>
        )
    }
}

export default Group;
