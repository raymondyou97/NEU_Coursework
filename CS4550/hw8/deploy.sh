#!/bin/bash

export MIX_ENV=prod
export PORT=4796
export NODEBIN=`pwd`/assets/node_modules/.bin
export PATH="$PATH:$NODEBIN"

echo "Building..."

mkdir -p ~/.config
mkdir -p priv/static

mix deps.get
mix compile
(cd assets && npm install)
(cd assets && webpack --mode production)
mix phx.digest

MIX_ENV=prod mix ecto.migrate

echo "Generating release..."
mix release

echo "Starting app..."

_build/prod/rel/taskTrackerSPA/bin/taskTrackerSPA foreground