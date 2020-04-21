class TheServer {
    getRequest(path, callback) {
        $.ajax(path, {
            method: "GET",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            success: callback,
            error: (resp) => {
                console.log("error", resp);
                alert("error");
            }
        });
    }

    deleteRequest(path, id, callback) {
        $.ajax(path + id, {
            method: "DELETE",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            success: callback,
            error: (resp) => {
                console.log("error", resp);
                alert("error");
            }
        });
    }

    postRequest(path, data, callback) {
        $.ajax(path, {
            method: "POST",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(data),
            success: callback,
            error: (resp) => {
                console.log("error", resp);
                alert("error");
            }
        });
    }

    patchRequest(path, data, callback) {
        $.ajax(path, {
            method: "PATCH",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(data),
            success: callback,
            error: (resp) => {
                console.log("error", resp);
                alert("error");
            }
        });
    }

    searchForRecipes(search_param, callback) {
        let encodedParams = encodeURIComponent(search_param);
        let params = { search_params: encodedParams };
        $.ajax('/api/v1/searchrecipe', {
            method: "POST",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(params),
            success: callback,
            error: (resp) => {
                console.log("error", resp);
                alert("error");
            }
        });
    }

    login(data, callback) {
        $.ajax("/api/v1/sessions", {
            method: "POST",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(data),
            success: callback,
            error: (resp) => {
                alert("Email and/or password incorrect or email.");
            }
        });
    }

    register(data, callback) {
        $.ajax("/api/v1/users", {
            method: "POST",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(data),
            success: callback,
            error: () => {
                alert("Error registering for a new account. Try again.");
            }
        });
    }

    addGroupRecipe(data, callback, error) {
        $.ajax('api/v1/groupsrecipes', {
            method: "POST",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: JSON.stringify(data),
            success: callback,
            error: error
        });
    }
}

export default new TheServer();