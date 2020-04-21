# Script for populating the database. You can run it as:
#
#     mix run priv/repo/seeds.exs
#
# Inside the script, you can read and write to any of your
# repositories directly:
#
#     FoodieFriends.Repo.insert!(%FoodieFriends.SomeSchema{})
#
# We recommend using the bang functions (`insert!`, `update!`
# and so on) as they will fail if something goes wrong.

alias FoodieFriends.Repo

alias FoodieFriends.Users.User

Repo.insert!(%User{email: "admin@admin.com", admin: true,
password_hash: "test", fname: "ray", lname: "you", gender: "male", age: 21})
Repo.insert!(%User{email: "test1@test.com", admin: false,
password_hash: "test", fname: "liz", lname: "cho", gender: "male", age: 11})
Repo.insert!(%User{email: "test2@test.com", admin: false,
password_hash: "test", fname: "kelvin", lname: "lin", gender: "female", age: 31})

alias FoodieFriends.Groups.Group

Repo.insert!(%Group{name: "420 squad", desc: "lit squad", owner_id: 1});
Repo.insert!(%Group{name: "northeastern", desc: "cs test test", owner_id: 2});
Repo.insert!(%Group{name: "fake group1", desc: "this is fake group1", owner_id: 3});
Repo.insert!(%Group{name: "fake group1", desc: "this is fake group2", owner_id: 1});

alias FoodieFriends.UsersGroups.UsersGroup

Repo.insert!(%UsersGroup{group_id: 1, user_id: 1});
Repo.insert!(%UsersGroup{group_id: 1, user_id: 2});
Repo.insert!(%UsersGroup{group_id: 1, user_id: 3});
Repo.insert!(%UsersGroup{group_id: 2, user_id: 1});

alias FoodieFriends.Recipes.Recipe
Repo.insert!(
    %Recipe{
        user_id: 1,
        recipe_id: "The-Best-Baked-Chicken-Legs-2690376",
        rating: 4,
        image_url: "https://lh3.googleusercontent.com/WB2kS5dfVhzEeMA2CtqHQxfvYypEuzewrQ3mdHYBZSzgMUeIWrbf_9_vK5_-TEXDsErxeI-Hid2RjxXEiFlJu7A=s90-c",
        name: "The Best Baked Chicken Legs",
        display_name: "Bless This Mess",
        courses: "Main Dishes",
        ingredients: "chicken legs, honey, soy sauce, ketchup, garlic, salt, pepper",
        cooktime: 3900
    }
);
Repo.insert!(
    %Recipe{
        user_id: 1,
        recipe_id: "The-Best-Baked-Chicken-Legs-2690376",
        rating: 4,
        image_url: "https://lh3.googleusercontent.com/WB2kS5dfVhzEeMA2CtqHQxfvYypEuzewrQ3mdHYBZSzgMUeIWrbf_9_vK5_-TEXDsErxeI-Hid2RjxXEiFlJu7A=s90-c",
        name: "test2",
        display_name: "test2",
        courses: "test2",
        ingredients: "asdasdasdasdasasdasdasdasdasd",
        cooktime: 3900
    }
);

alias FoodieFriends.Messages.Message
Repo.insert!(%Message{msg: "hello", group_id: 1, user_id: 1});
Repo.insert!(%Message{msg: "its me", group_id: 1, user_id: 1});
Repo.insert!(%Message{msg: "i love web dev", group_id: 1, user_id: 2});

alias FoodieFriends.GroupsRecipes.GroupsRecipe
Repo.insert!(%GroupsRecipe{group_id: 1, recipe_id: 1});
Repo.insert!(%GroupsRecipe{group_id: 1, recipe_id: 2});