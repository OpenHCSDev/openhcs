#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "$1" "$2"
test ! -e "/tmp/.X11-unix/X$FLEET_DISPLAY"
test ! -e "/tmp/.X$FLEET_DISPLAY-lock"
exec /usr/bin/Xvfb ":$FLEET_DISPLAY" -screen 0 1600x1000x24 -nolisten tcp -s 0
