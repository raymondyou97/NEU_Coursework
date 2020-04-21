#!/bin/bash

export MIX_ENV=prod
export PORT=4797
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

MIX_ENV=prod mix ecto.reset
MIX_ENV=prod mix run priv/repo/seeds.exs

echo "Generating release..."
mix release

echo "Starting app..."

_build/prod/rel/foodiefriends/bin/foodiefriends foreground