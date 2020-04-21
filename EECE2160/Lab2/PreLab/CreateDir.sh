#!/bin/bash
# input-user.bash
echo -n "Enter name for directory:"
read -r name
mkdir "$name"