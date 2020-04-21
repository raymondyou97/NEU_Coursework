# Script for populating the database. You can run it as:
#
#     mix run priv/repo/seeds.exs
#
# Inside the script, you can read and write to any of your
# repositories directly:
#
#     TaskTrackerSPA.Repo.insert!(%TaskTrackerSPA.SomeSchema{})
#
# We recommend using the bang functions (`insert!`, `update!`
# and so on) as they will fail if something goes wrong.

alias TaskTrackerSPA.Repo
alias TaskTrackerSPA.Users.User

Repo.insert!(%User{email: "alice@example.com", admin: true, password_hash: "password"})
Repo.insert!(%User{email: "bob@example.com", admin: false, password_hash: "password"})
Repo.insert!(%User{email: "a", admin: false, password_hash: "a"})

alias TaskTrackerSPA.Tasks.Task

Repo.insert!(%Task{title: "test1", desc: "test1", time: 0, completed: false, user_id: 1})
Repo.insert!(%Task{title: "test2", desc: "test2", time: 15, completed: true, user_id: 1})