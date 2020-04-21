#!/bin/bash

export MIX_ENV=prod
export PORT=4793

echo "Stopping old copy of app, if any..."

_build/prod/rel/battleships/bin/battleships stop || true

echo "Starting app..."

_build/prod/rel/battleships/bin/battleships foreground