import React from 'react';
import _ from 'lodash';
import api from '../utils/api';
import cookie_helper from '../utils/cookie_helper';

class MyRecipes extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            user_id: -1,
            recipes: [],
            myGroups: [],
            //opened recipe
            currentRecipeName: "",
            currentRating: -1,
            currentPrepTime: "",
            currentCookTime: "",
            currentImage: "",
            currentNumberOfServings: "",
            currentYield: "",
            currentAttribution: "",
            currentCourses: "",
            currentSourceName: "",
            currentSourceURL: "",
            currentIngredientLines: [],
        };
        this.setGroups();
    }

    componentDidMount() {
        this.getRecipes();
        let user_session = cookie_helper.getUserSession();
        user_session ? this.setState({
            user_id: user_session.user_id
        }) : null;
    }

    getRecipes() {
        api.getRequest('api/v1/recipes', (resp) => {
            //hard coded user_id rn, eventually hook up when log in done
            let filteredRecipes = resp.data.filter(recipe => {
                return recipe.user_id === this.state.user_id
            });
            this.setState({
                recipes: filteredRecipes
            });
        });
    }

    deleteRecipe(id) {
        alert("Are you sure you want to delete this recipe?");
        api.deleteRequest('api/v1/recipes/', id, (resp) => {
            let filteredRecipes = this.state.recipes.filter(recipe => {
                return recipe.id !== id
            });
            this.setState({
                recipes: filteredRecipes
            });
        })
    }

    viewRecipe(recipe_id) {
        api.getRequest(`/api/v1/searchrecipe/${recipe_id}`, (data) => {
            let currentRecipe = data.data;
            let currentCourses = "";
            if (currentRecipe.attributes && currentRecipe.attributes.course && currentRecipe.attributes.course.length > 0) {
                currentCourses = currentRecipe.attributes.course.join(", ");
            }
            //add more attributes
            this.setState({
                currentRecipeName: currentRecipe.name,
                currentRating: currentRecipe.rating,
                currentPrepTime: currentRecipe.prepTime,
                currentCookTime: currentRecipe.totalTime,
                currentImage: currentRecipe.images[0].imageUrlsBySize[90],
                currentNumberOfServings: currentRecipe.numberOfServings,
                currentYield: currentRecipe.yield,
                currentAttribution: currentRecipe.attribution.html,
                currentCourses: currentCourses,
                currentSourceName: currentRecipe.source.sourceDisplayName,
                currentSourceURL: currentRecipe.source.sourceRecipeUrl,
                currentIngredientLines: currentRecipe.ingredientLines
            });
        });
    }

    setGroups() {
        api.getRequest('api/v1/usersgroups', (resp) => {
            let filteredUsersGroups = resp.data.filter(usersgroup => {
                return usersgroup.user_id === this.state.user_id
            });
            this.getGroupsByUsersGroups(filteredUsersGroups);
        });
    }

    getGroupsByUsersGroups(usersgroups) {
        let curr = this.state.myGroups;
        usersgroups.forEach(usersgroup => {
            api.getRequest('api/v1/groups/' + usersgroup.group_id, (resp) => {
                curr.push(resp.data);
                this.setState({
                    myGroups: curr
                });
            });
        });
    }

    addRecipeToGroup(group_id, recipe_idx) {
        let selectedRecipe = this.state.recipes[recipe_idx];
        let newGroupsRecipe = {
            groups_recipe: {
                group_id: group_id,
                recipe_id: selectedRecipe.id
            }
        };
        api.addGroupRecipe(newGroupsRecipe, () => {
            alert("Successfully added!");
        }, () => {
            alert("Recipe already exists in group...")
        });
    }

    getGroupOptionSelector(recipe_idx) {
        let components = [];
        this.state.myGroups.forEach(group => {
            components.push(<a className="dropdown-item" key={group.id} value={group.id} onClick={() => this.addRecipeToGroup(group.id, recipe_idx)}>{group.name}</a>);
        });
        return (
            <div className="dropdown">
                <button className="btn btn-info dropdown-toggle special-btn" type="button" id="dropdownMenuButton" data-toggle="dropdown" aria-haspopup="true" aria-expanded="false">Add To Group</button>
                <div className="dropdown-menu" aria-labelledby="dropdownMenuButton">
                    {components}
                </div>
            </div>
        )
    }

    displayRecipes() {
        if (this.state.recipes.length > 0) {
            return (
                <div>
                    <div className="row">
                        {this.state.recipes.map((recipe, idx) =>
                            <div key={recipe.id} className="card" style={{ width: '16.5rem' }}>
                                <img className="card-img-top" src={recipe.image_url} alt="recipe-img"></img>
                                <div className="card-body">
                                    <h5 className="card-title">{recipe.name}</h5>
                                    <p className="card-text">({recipe.display_name})</p>
                                    <div className="modal-body">
                                        <div>
                                            <span className="recipe-column">Rating: </span>
                                            {recipe.rating}
                                        </div>
                                        <div>
                                            <span className="recipe-column">Cooktime (in seconds): </span>
                                            {recipe.cooktime}
                                        </div>
                                        {recipe.courses && recipe.courses.length > 0 &&
                                            <div>
                                                <span className="recipe-column">Courses: </span>
                                                {recipe.courses}
                                            </div>
                                        }
                                        {recipe.ingredients && recipe.ingredients.length > 0 &&
                                            <div>
                                                <span className="recipe-column">Ingredients: </span>
                                                {recipe.ingredients}
                                            </div>
                                        }
                                    </div>
                                    <button className="btn btn-primary btn-block" onClick={() => this.viewRecipe(recipe.recipe_id)} data-toggle="modal" data-target="#myRecipeDetailModal">View Details</button>
                                    <button className="btn btn-danger btn-block" onClick={() => this.deleteRecipe(recipe.id)}>Delete</button>
                                    {this.getGroupOptionSelector(idx)}
                                </div>
                            </div>
                        )}
                    </div>
                </div>
            )
        }
        else {
            return <h5>You currently have no recipes. Add some recipes!</h5>
        }
    }

    displayModal() {
        return (
            <div className="modal fade" id="myRecipeDetailModal" tabIndex="-1" role="dialog">
                <div className="modal-dialog modal-dialog-centered" role="document">
                    <div className="modal-content">
                        <div className="modal-header">
                            <h3 className="modal-title" id="recipeDetailModalTitle">{this.state.currentRecipeName}</h3>
                            <img className="card-img-top" src={this.state.currentImage} alt="recipe-img"></img>
                        </div>
                        <div className="modal-body">
                            {this.state.currentYield &&
                                <div>
                                    <span className="recipe-column">Yield: </span>
                                    {this.state.currentYield}
                                </div>
                            }
                            {this.state.currentNumberOfServings &&
                                <div>
                                    <span className="recipe-column">Number of servings: </span>
                                    {this.state.currentNumberOfServings}
                                </div>
                            }
                            {this.state.currentRating &&
                                <div>
                                    <span className="recipe-column">Rating: </span>
                                    {this.state.currentRating} / 5
                                </div>
                            }
                            {this.state.currentPrepTime &&
                                <div>
                                    <span className="recipe-column">Preparation time: </span>
                                    {this.state.currentPrepTime}
                                </div>

                            }
                            {this.state.currentCookTime &&
                                <div>
                                    <span className="recipe-column">Cook time: </span>
                                    {this.state.currentCookTime}
                                </div>
                            }
                            {this.state.currentCourses &&
                                <div>
                                    <span className="recipe-column">Course(s): </span>
                                    {this.state.currentCourses}
                                </div>
                            }
                            {this.state.currentIngredientLines &&
                                <div>
                                    <span className="recipe-column">Ingredient(s): </span>
                                    <ul>
                                        {this.state.currentIngredientLines.map((ing, idx) =>
                                            <li key={idx}>{ing}</li>
                                        )}
                                    </ul>
                                </div>
                            }
                            {this.state.currentSourceName &&
                                <div>
                                    <span className="recipe-column">Source: </span>
                                    <a href={this.state.currentSourceURL}>
                                        {this.state.currentSourceName}
                                    </a>
                                </div>
                            }
                        </div>
                        <div className="modal-footer">
                            <div dangerouslySetInnerHTML={{ __html: this.state.currentAttribution }}></div>
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
                <h3>My Recipes</h3>
                {this.displayRecipes()}
                {this.displayModal()}
            </div>
        )
    }
}

export default MyRecipes;
