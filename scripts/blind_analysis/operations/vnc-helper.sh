#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "$1" "$2"
test "$FLEET_PARENT_RELEASED" = 1
systemctl --user is-active --quiet "$FLEET_HELPER_UNIT-x$FLEET_DISPLAY.scope"
systemctl --user is-active --quiet "$FLEET_HELPER_UNIT-wm$FLEET_DISPLAY.scope"
exec /usr/bin/x11vnc -display ":$FLEET_DISPLAY" -localhost -rfbport "$FLEET_VNC" -nopw -forever -shared -noxdamage -viewonly
