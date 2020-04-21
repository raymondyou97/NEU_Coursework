import React from 'react';
import _ from 'lodash';
import api from '../utils/api';
import cookie_helper from '../utils/cookie_helper';

class RecipeSearch extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            search_param: "",
            recipes: [],
            myGroups: [],
            user_id: this.getUserId(),
            showRecipes: true,
            //need attribution in order to abide by api rules
            attribution: "",
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
            //pagination, 12 items per page, 60 loaded per search
            currentShownRecipes: [],
            currentPage: 0
        };
        this.chunkedRecipes = [];
        this.numberOfPages = 0;
    }

    getUserId() {
        let user_session = cookie_helper.getUserSession();
        return user_session ? user_session.user_id : null;
    }


    handleSearchParamChange(e) {
        this.setState({ search_param: e.target.value });
    }

    searchForRecipes(e) {
        if (e.keyCode === 13 || e.type === 'click') {
            api.searchForRecipes(this.state.search_param, (resp) => {
                this.chunkedRecipes = _.chunk(resp.data.matches, 12);
                this.numberOfPages = Math.ceil(resp.data.matches.length / 12);
                this.setState({
                    attribution: resp.data.attribution.html,
                    recipes: resp.data.matches,
                    showRecipes: true,
                    currentShownRecipes: resp.data.matches.slice(0, 12)
                });
            });
        }
    }

    addRecipe(idx) {
        let user_session = cookie_helper.getUserSession();
        if (user_session) {
            let user_id = user_session.user_id;
            alert("Are you sure you want to add this recipe?");
            let selectedRecipe = this.state.recipes[idx];

            let ingredients = selectedRecipe.ingredients ? selectedRecipe.ingredients.join(', ') : "";
            let courses = selectedRecipe.attributes.course ? selectedRecipe.attributes.course.join(', ') : "";

            let recipeObj = {
                recipe: {
                    user_id: user_id,
                    recipe_id: selectedRecipe.id,
                    rating: selectedRecipe.rating,
                    display_name: selectedRecipe.sourceDisplayName,
                    name: selectedRecipe.recipeName,
                    ingredients: ingredients,
                    image_url: selectedRecipe.imageUrlsBySize[90],
                    courses: courses,
                    cooktime: selectedRecipe.totalTimeInSeconds
                }
            };
            api.postRequest('/api/v1/recipes', recipeObj, (resp) => console.log(resp));;
            location.reload();
        } else {
            alert("Log in to save recipes!");
        }
    }

    showDetails(idx) {
        let recipe_id = this.state.recipes[idx].id;

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
    
    getGroupsByUsersGroups(usersgroups) {
        let curr = this.state.myGroups;
        usersgroups.forEach(usersgroup => {
            api.getRequest('api/v1/groups/' + usersgroup.group_id, (resp) => {
                curr.push(resp.data);
                return curr;
            });
        });

    }

    displayRecipes() {
        if (this.state.currentShownRecipes.length > 0 && this.state.showRecipes) {
            return (
                <div>
                    <nav className="pagination-block">
                        <ul className="pagination">
                            <li className="page-item">
                                <a className="page-link page-link-btn" onClick={() => this.previousPage()}>Previous</a>
                            </li>
                            {this.getPageNumbers()}
                            <li className="page-item">
                                <a className="page-link page-link-btn" onClick={() => this.nextPage()}>Next</a>
                            </li>
                        </ul>
                    </nav>
                    <div className="recipe-block">
                        <div className="row">
                            {this.state.currentShownRecipes.map((recipe, idx) =>
                                <div key={recipe.id} className="card" style={{ width: '16.5rem' }}>
                                    <img className="card-img-top" src={recipe.imageUrlsBySize[90]} alt="recipe-img"></img>
                                    <div className="card-body">
                                        <h5 className="card-title">{recipe.recipeName}</h5>
                                        <p className="card-text">({recipe.sourceDisplayName})</p>
                                        <button className="btn btn-primary btn-block" onClick={() => this.addRecipe(idx)}>Add To My Recipes</button>
                                        <button className="btn btn-secondary btn-block" onClick={() => this.showDetails(idx)} data-toggle="modal" data-target="#recipeDetailModal">View Details</button>
                                    </div>
                                </div>
                            )}
                        </div>
                        <div className="api-watermark" dangerouslySetInnerHTML={{ __html: this.state.attribution }}></div>
                    </div>
                    <nav className="pagination-block">
                        <ul className="pagination">
                            <li className="page-item">
                                <a className="page-link page-link-btn" onClick={() => this.previousPage()}>Previous</a>
                            </li>
                            {this.getPageNumbers()}
                            <li className="page-item">
                                <a className="page-link page-link-btn" onClick={() => this.nextPage()}>Next</a>
                            </li>
                        </ul>
                    </nav>
                </div>
            )
        }
    }

    toggleRecipeResults() {
        let newState = !this.state.showRecipes;
        this.setState({
            showRecipes: newState
        });
    }

    previousPage() {
        let newPage = this.state.currentPage - 1;
        if (newPage < 0) {
            return;
        }
        this.setState({
            currentShownRecipes: this.chunkedRecipes[newPage],
            currentPage: newPage
        });
    }

    nextPage() {
        let newPage = this.state.currentPage + 1;
        if (newPage >= this.numberOfPages) {
            return;
        }
        this.setState({
            currentShownRecipes: this.chunkedRecipes[newPage],
            currentPage: newPage
        });
    }

    goToPage(idx) {
        this.setState({
            currentShownRecipes: this.chunkedRecipes[idx],
            currentPage: idx
        });
    }

    getPageNumbers() {
        let pages = [];
        for (let i = 0; i < this.numberOfPages; i++) {
            if (this.state.currentPage == i) {
                pages.push(
                    <li key={i} className="page-item active">
                        <a className="page-link" onClick={() => this.goToPage(i)}>{i + 1}</a>
                    </li>);
            }
            else {
                pages.push(
                    <li key={i} className="page-item">
                        <a className="page-link" onClick={() => this.goToPage(i)}>{i + 1}</a>
                    </li>);
            }
        }
        return pages;
    }

    displayModal() {
        return (
            <div className="modal fade" id="recipeDetailModal" tabIndex="-1" role="dialog">
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
                <div className="row">
                    <div className="col-xl">
                        <input type="search-recipes" className="form-control" id="search-recipes" onKeyDown={(e) => this.searchForRecipes(e)}
                            placeholder="Search for recipes" onChange={(e) => this.handleSearchParamChange(e)}></input>
                    </div>
                </div>
                <div className="row search-row">
                    <div className="col-sm">
                        <button className="btn btn-primary search-btn" id="search-recipes-btn" onClick={(e) => this.searchForRecipes(e)}>Search</button>
                    </div>
                    {this.state.currentShownRecipes.length > 0 &&
                        <div className="col-sm">
                            <button className="btn btn-secondary search-btn" onClick={() => this.toggleRecipeResults()}>Show/Hide Results</button>
                        </div>
                    }
                </div>
                {this.displayRecipes()}
                {this.displayModal()}
            </div>
        )
    }
}

export default RecipeSearch;
