#!/bin/bash

export MIX_ENV=prod
export PORT=4797

echo "Stopping old copy of app, if any..."

_build/prod/rel/foodiefriends/bin/foodiefriends stop || true

echo "Starting app..."

_build/prod/rel/foodiefriends/bin/foodiefriends foreground