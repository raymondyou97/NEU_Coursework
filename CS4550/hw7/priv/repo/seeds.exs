# Script for populating the database. You can run it as:
#
#     mix run priv/repo/seeds.exs
#
# Inside the script, you can read and write to any of your
# repositories directly:
#
#     TaskTracker.Repo.insert!(%TaskTracker.SomeSchema{})
#
# We recommend using the bang functions (`insert!`, `update!`
# and so on) as they will fail if something goes wrong.

alias TaskTracker.Repo
alias TaskTracker.Users.User
alias TaskTracker.Tasks.Task

Repo.insert!(%User{email: "principal@test.com", name: "nat"})
Repo.insert!(%User{email: "teacher1@test.com", name: "alice", supervisor_id: 1})
Repo.insert!(%User{email: "teacher2@test.com", name: "tuck", supervisor_id: 1})
Repo.insert!(%User{email: "student1@test.com", name: "bob", supervisor_id: 2})
Repo.insert!(%User{email: "student2@test.com", name: "john", supervisor_id: 2})
Repo.insert!(%User{email: "student3@test.com", name: "liz", supervisor_id: 3})
Repo.insert!(%User{email: "student4@test.com", name: "kristy", supervisor_id: 3})

Repo.insert!(%Task{title: "eat1", description: "eat more", completed: true, user_id: 2})
Repo.insert!(%Task{title: "eat2", description: "eat more2", completed: false, user_id: 2})
Repo.insert!(%Task{title: "eat3", description: "eat more3", completed: false, user_id: 2})
Repo.insert!(%Task{title: "eat4", description: "eat more4", completed: false, user_id: 2})
Repo.insert!(%Task{title: "eat3", description: "eat more3", completed: true, user_id: 3})
Repo.insert!(%Task{title: "eat4", description: "eat more4", completed: false, user_id: 3})
