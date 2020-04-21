// We need to import the CSS so that webpack will load it.
// The MiniCssExtractPlugin is used to separate it out into
// its own CSS file.
import css from "../css/app.scss";

// webpack automatically bundles all modules in your
// entry points. Those entry points can be configured
// in "webpack.config.js".
//
// Import dependencies
//
import "phoenix_html";
import jQuery from 'jquery';
window.jQuery = window.$ = jQuery;
import "bootstrap";

// Import local files
//
// Local files can be imported directly using relative paths, for example:
// import socket from "./socket"

$(document).ready(function () {
    $(".end-task-btn").attr("disabled", true);

    $(".start-task-btn").on("click", function () {
        let startTime = new Date().toISOString();

        $(this).parent().append("<span>" + startTime + "</span");
        $(this).parent().find("span").first().hide();
        $(this).prop("disabled", true);
        $(this).parent().find(".end-task-btn").prop("disabled", false);

        //display in client
        $(this).parent().parent().find(".timeblock-container").append(
            "<li class='timeblock-entry'>" +
                "<div class='timeblock-info'>" +
                    "<div>Start datetime: <span class='time-block-value'>"+ startTime.replace("T", " ") + "</span></div>" +
            "</li>"
        );
    });

    $(".end-task-btn").on("click", function () {
        let taskId = $(this).parent().parent().find(".task-id").html();
        let startTime = $(this).parent().find("span").first().html();
        let endTime = new Date().toISOString();

        let data = JSON.stringify({
            timeblock: {
                start: startTime,
                end: endTime,
                task_id: parseInt(taskId),
            },
        });

        $.ajax("ajax/timeblocks", {
            method: "post",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: data,
            success: (resp) => {
                $(this).parent().find(".start-task-btn").prop("disabled", false);
                $(this).prop("disabled", true);
                $(this).parent().find("span").first().remove();
                $(this).parent().parent().find(".timeblock-info").last().append("<div>End datetime: <span class='time-block-value'>" + resp.data.end.replace("T", " ") + "</span></div>");
                $(this).parent().parent().find(".timeblock-entry").last().append(
                    "<div class='timeblock-btns'>" +
                        "<button id=" + resp.data.id + " class='btn btn-info btn-sm timeblock-edit'>Edit</button>" +
                        "<button id=" + resp.data.id + " class='btn btn-warning btn-sm timeblock-delete'>Delete</button>" +
                    "</div>");

                //need to rebind listeners
                $(".timeblock-delete").on("click", function() {
                    deleteOnClick($(this));
                });
            
                $(".timeblock-edit").on("click", function() {
                    editOnClick($(this));
                });
            },
            error: (resp) => {
                console.log(resp);
            }
        });
    });

    $(".timeblock-delete").on("click", function() {
        deleteOnClick($(this));
    });

    $(".timeblock-edit").on("click", function() {
        editOnClick($(this));
    });

    $(".submit-edit-changes").on("click", function() {
        let newStart = $(this).parent().find(".start_datetime").val() + "T00:00:00.000Z";
        let newEnd = $(this).parent().find(".end_datetime").val() + "T00:00:00.000Z";
        let taskId = $(".task-id-here").html();

        let data = JSON.stringify({
            timeblock: {
                start: newStart,
                end: newEnd,
                task_id: parseInt(taskId)
            },
        });

        let timeblock_id = $(this).attr("id");

        $.ajax("ajax/timeblocks/" + timeblock_id, {
            method: "put",
            dataType: "json",
            contentType: "application/json; charset=UTF-8",
            data: data,
            success: (resp) => {
                let updateStart = resp.data.start.replace("T", " ");
                let updateEnd = resp.data.end.replace("T", " ");
                $(".success-edit").show();
                $(".submit-edit-changes").hide();
                $(".cancel-edit-changes").hide();
                $(".success-edit-text").html("Successful update!!!");

                $(".active-edit-area").find(".timeblock-info").find(".time-block-value").eq(0).html(updateStart);
                $(".active-edit-area").find(".timeblock-info").find(".time-block-value").eq(1).html(updateEnd);
            },
            error: (resp) => {
                $(".error-edit").html("Error updating. Data is in invalid format!!!")
            }
        });
    });

    $(".cancel-edit-changes").on("click", function() {
        $(".edit-task-block").hide();
    });

    $(".hide-edit-changes").on("click", function() {
        $(".edit-task-block").hide();
        $(".success-edit").hide();
    });

    function editOnClick(incoming) {
        $(".submit-edit-changes").show();
        $(".cancel-edit-changes").show();
        $(".edit-task-block").show();
        let oldStart = incoming.parent().parent().find(".time-block-value").eq(0).html();
        let oldEnd = incoming.parent().parent().find(".time-block-value").eq(1).html();
        $(".start_datetime").val(oldStart.substring(0, 10));
        $(".end_datetime").val(oldEnd.substring(0, 10));
        let id = incoming.attr("id");
        $(".submit-edit-changes").attr("id", id);
        $(".task-id-here").html(incoming.parent().parent().parent().parent().parent().find(".task-id").html());
    
        $(".active-edit-area").removeClass("active-edit-area");
        incoming.parent().parent().addClass("active-edit-area");
    }
    
    function deleteOnClick(incoming) {
        if (confirm('Are you sure?')) {
            let id = incoming.attr("id");
            $.ajax("ajax/timeblocks/" + id, {
                method: "delete",
                success: (resp) => {
                    incoming.parent().parent().remove();
                },
                error: (resp) => {
                    console.log(resp);
                }
            });
        }
    }
});