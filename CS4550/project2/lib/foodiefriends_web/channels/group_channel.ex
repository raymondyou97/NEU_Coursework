defmodule FoodieFriendsWeb.GroupChatChannel do
    use FoodieFriendsWeb, :channel

    alias FoodieFriends.GroupChat
  
    def join("groupchat:" <> group_id, payload, socket) do
      if authorized?(payload) do
        group_id = String.to_integer(group_id)
        user_id = Map.get(payload, "user_id")
        socket = socket
          |> assign(:group_id, group_id)
        {:ok, %{"group_id" => group_id, "user_id" => user_id, "data" => GroupChat.client_view(group_id)}, socket}
      else
        {:error, %{reason: "unauthorized"}}
      end
    end

    def handle_in("newMessage", nil, socket) do
      group_id = socket.assigns[:group_id]
      data = GroupChat.client_view(group_id)
      broadcast!(socket, "everyoneNewMessage", data)
      {:noreply, socket}
    end
  
    defp authorized?(_payload) do
      true
    end
  end