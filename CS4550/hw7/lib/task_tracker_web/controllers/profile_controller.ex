defmodule TaskTrackerWeb.ProfileController do
    use TaskTrackerWeb, :controller
  
    alias TaskTracker.Users
    alias TaskTracker.Users.User
  
    def index(conn, _params) do
      conn = fetch_session(conn)
      userModel = conn.assigns[:current_user]
      fields = User.__schema__(:fields)
      fieldModel = Map.take(userModel, fields)

      currentUser = Users.get_user!(fieldModel[:id])
      underlings = Users.get_underlings(fieldModel[:id])
      if fieldModel[:supervisor_id] do
        supervisor = Users.get_user!(fieldModel[:supervisor_id])
        render(conn, "index.html", currentUser: currentUser, supervisor: supervisor, underlings: underlings)
      else
        render(conn, "index.html", currentUser: currentUser, supervisor: nil, underlings: underlings)
      end
    end
  end
  