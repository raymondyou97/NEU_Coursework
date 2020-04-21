import React from 'react';
import _ from 'lodash';
import api from '../utils/api';
import socket from '../socket';
import cookie_helper from '../utils/cookie_helper';

class GroupChat extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            user_id: null,
            email: null,
            group_id: null,
            messages: [],
            joined: false,
            active_groups: []
        };
    }

    componentWillMount() {
        this.getUserData();
        this.getAvailableGroupIds();
    }

    getUserData() {
        let user_session = cookie_helper.getUserSession();
        if (user_session) {
            this.setState({
                email: user_session.email,
                user_id: user_session.user_id
            });
        }
    }

    getAvailableGroupIds() {
        api.getRequest("/api/v1/usersgroups", (groups) => {
            let active_groups = groups.data.filter(group => {
                return group.user_id === this.state.user_id
            });
            this.setState({
                active_groups: active_groups
            });
        })
    }

    joinChannel() {
        let group_id = $("#select-group-id option:selected").val();
        //still default value
        if (group_id === "-1") {
            return;
        }
        this.channel = socket.channel(`groupchat:${group_id}`, {
            "user_id": this.state.user_id
        });
        this.channel.join()
            .receive("ok", (view) => {
                this.setState({
                    messages: view.data.messages,
                    group_id: group_id,
                    joined: true
                });
                this.attachChannelListeners();
            })
            .receive("error", (resp) => {
                console.log("Unable to join", resp)
            });
    }

    leaveChannel() {
        this.channel = null;
        this.resetGroup();
    }

    resetGroup() {
        this.setState({
            group_id: null,
            messages: [],
            joined: false
        });
    }

    attachChannelListeners() {
        this.channel.on("everyoneNewMessage", (data) => {
            this.setState({
                messages: data.messages
            });
        });
    }

    toggleChatContainer() {
        if ($(".toggle-container").is(':visible')) {
            $(".toggle-container").hide();
            $(".footer-btn-container").addClass("footer-btn-container-hidden");
            $(".btn-toggle-chat").html("\\/");
        }
        else {
            $(".toggle-container").show();
            $(".footer-btn-container").removeClass("footer-btn-container-hidden");
            $(".btn-toggle-chat").html("/\\");
        }
    }

    deleteMessage(message) {
        let id = message.msg_id;
        api.deleteRequest("/api/v1/messages/", id, () => {
            let newMsgs = this.state.messages.filter(msg => {
                return msg.msg_id !== id;
            });
            this.setState({
                messages: newMsgs
            });
            this.getChatView();
        });
    }

    getChatView() {
        if (this.state.messages.length > 0) {
            let sortedMsgs = this.state.messages.sort((a, b) => {
                let dateA = new Date(a.timestamp);
                let dateB = new Date(b.timestamp);
                return dateA - dateB;
            });
            let view = sortedMsgs.map((message, idx) => {
                return (
                    <div key={idx} className={"single-msg-block " + (message.user_id === this.state.user_id ? "my-msg" : "not-my-msg")}>
                        <div className="msg-sender" data-toggle="tooltip" data-placement="left"
                            title={message.timestamp}>{message.user_fname} {message.user_lname} ({message.user_email}): </div>
                        <div className="msg">{message.msg}</div>
                        {message.user_id === this.state.user_id &&
                            <div className="msg-delete">
                                <button className="btn btn-danger msg-delete-btn" onClick={() => this.deleteMessage(message)}>X</button>
                            </div>
                        }
                    </div>
                )
            })
            return view;
        }
        else {
            return (
                <div>No messages currently in group.</div>
            )
        }
    }

    sendMessage(e) {
        if (e.keyCode === 13 || e.type === 'click') {
            let newMsg = {
                message: {
                    group_id: Number(this.state.group_id),
                    user_id: this.state.user_id,
                    msg: $("#chat-msg-input").val()
                }
            };
            api.postRequest("/api/v1/messages", newMsg, (data) => {
                this.channel.push("newMessage");
                $("#chat-msg-input").val('');
            })
        }
    }

    getJoinGroupView() {
        let options = this.state.active_groups.map(group => {
            let text = `Group ID: ${group.group_id} | Group Name: ${group.group_name} | Group Description: ${group.group_desc}`
            return (<option key={group.id} value={group.group_id}>{text}</option>)
        })
        options.unshift(<option key={-1} value={-1}>Join one of your available group chats!</option>);
        return (
            <div>
                <select className="form-control join-group-select" id="select-group-id">
                    {options}
                </select>
                <button className="btn btn-outline-primary" onClick={() => this.joinChannel()}>Join Chat</button>
            </div>
        )
    }

    getFooterButtonView() {
        if (this.state.joined) {
            return (
                <div>
                    <button className="btn btn-primary btn-toggle-chat" onClick={() => this.toggleChatContainer()}>/\</button>
                    <button className="btn btn-danger" onClick={() => this.leaveChannel()}>Leave</button>
                </div>
            )
        }
        else {
            let joinGroupView = this.getJoinGroupView();
            return joinGroupView;
        }
    }

    render() {
        let view;
        if (this.state.email) {
            view = <div className="whole-footer">
                <div className={"footer-btn-container " + (this.state.joined ? '' : 'move-down')}>
                    <div className="btn-container">
                        {this.getFooterButtonView()}
                    </div>
                </div>
                {this.state.joined &&
                    <div className="toggle-container">
                        <div className="footer">
                            <div className="chat-container">
                                <h5 className="group-chat-title">Group Chat (ID: {this.state.group_id})</h5>
                                <div>Hover over name to see timestamp of message</div>
                                {this.getChatView()}
                                <div className="last-msg"></div>
                            </div>
                        </div>
                        <div className="chat-input-bar">
                            <input className="chat-msg-input" type="text" id="chat-msg-input" name="msg-input" placeholder="Enter your message" onKeyDown={(e) => this.sendMessage(e)}></input>
                            <button className="chat-msg-btn" onClick={(e) => this.sendMessage(e)}>Send</button>
                        </div>
                    </div>
                }
            </div>
        }
        else {
            view = "";
        }
        return view;
    }
}

export default GroupChat;