#!/bin/bash

export MIX_ENV=prod
export PORT=4796

echo "Stopping old copy of app, if any..."

_build/prod/rel/taskTrackerSPA/bin/taskTrackerSPA stop || true

echo "Starting app..."

_build/prod/rel/taskTrackerSPA/bin/taskTrackerSPA foreground