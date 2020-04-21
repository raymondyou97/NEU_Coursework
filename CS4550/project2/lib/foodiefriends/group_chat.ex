defmodule FoodieFriends.GroupChat do
    import Ecto.Query, warn: false

    alias FoodieFriends.Messages

    def client_view(group_id) do
        group_data = Messages.list_messages_by_group_id(group_id)
        
        %{
            messages: group_data
        }
    end
  end
  
  