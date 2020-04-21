import React from 'react';
import _ from 'lodash';
import api from '../utils/api';
import cookie_helper from '../utils/cookie_helper';

class MyGroups extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            myGroups: [],
            allUserGroups: [],
            allGroupRecipesNoFilter: [],
            allRecipes: [],
            user_id: "",
            //modal stuff
            current_group_name: "",
            current_group_desc: "",
            current_group_members: [],
            current_recipes: []
        };
    }

    componentDidMount() {
        this.getUserData();
        this.getAllGroups();
        this.getGroupRecipes();
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
                let myGroupsIds = usersgroups.data.filter(group => {
                    return group.user_id === this.state.user_id;
                }).map(group => group.group_id);
                let myGroups = groups.data.filter(group => {
                    return myGroupsIds.includes(group.id);
                });
                this.setState({
                    myGroups: myGroups,
                    allUserGroups: usersgroups.data
                });
                this.getGroupView();
            })
        });
    }

    getGroupRecipes() {
        api.getRequest('api/v1/groupsrecipes', (gp) => {
            this.setState({
                allGroupRecipesNoFilter: gp.data
            });
            let recipeIDs = gp.data.map(i => {
                return i.recipe_id;
            });

            for (let i = 0; i < recipeIDs.length; i++) {
                api.getRequest(`api/v1/recipes/${recipeIDs[i]}`, (recipe) => {
                    let newState = this.state.allRecipes.concat(recipe.data);
                    this.setState({
                        allRecipes: newState
                    });
                })
            }
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

        let currentGroup = this.state.myGroups.find(group => group.id === group_id);
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
        let specificRecipeList = [];
        for (let i = 0; i < this.state.allGroupRecipesNoFilter.length; i++) {
            for (let j = 0; j < this.state.allRecipes.length; j++) {
                if (this.state.allGroupRecipesNoFilter[i].group_id === group_id) {
                    if (this.state.allGroupRecipesNoFilter[i].recipe_id === this.state.allRecipes[j].id) {

                        specificRecipeList.push(this.state.allRecipes[j]);
                    }
                }
            }
        }

        this.setState({
            current_group_name: currentGroup.name,
            current_group_desc: currentGroup.desc,
            current_recipes: specificRecipeList
        });
        $('#groupInfoModal').modal('toggle')
    }

    getGroupView() {
        let myGroupIds = this.state.allUserGroups.filter(group => {
            return group.user_id === this.state.user_id
        }).map(group => group.group_id);

        let view = this.state.myGroups.map(group => {
            if (myGroupIds.includes(group.id)) {
                return (
                    <tr key={group.id}>
                        <td>{group.id}</td>
                        <td>{group.name}</td>
                        <td>{group.desc}</td>
                        <td>
                            <button className="btn btn-danger" onClick={() => this.leaveGroup(group.id)}>Leave</button>
                            <button className="btn btn-info" onClick={() => this.viewDetails(group.id)}>View Details</button>
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
                    {this.getRecipeCards()}
                </div>
            )
        }
        else {
            return <span> 0</span>
        }
    }

    getRecipeCards() {
        return (
            <div>
                <span className="group-column">Recipes in this group:</span>
                {this.state.current_recipes.length > 0 ?
                    <div className="row">
                        {this.state.current_recipes.map((recipe, idx) =>
                            <div key={recipe.id} className="card" style={{ width: '16.5rem' }}>
                                <img className="card-img-top" src={recipe.image_url} alt="recipe-img"></img>
                                <div className="card-body">
                                    <h5 className="card-title">{recipe.name}</h5>
                                    <p className="card-text">({recipe.display_name})</p>
                                </div>
                            </div>
                        )}
                    </div> : <span> 0</span>
                }
            </div>
        );
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
            </div>
        )
    }
}

export default MyGroups;
