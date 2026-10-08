#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "$1" "$2"
systemctl --user is-active --quiet "$FLEET_HELPER_UNIT-x$FLEET_DISPLAY.scope"
systemctl --user is-active --quiet "$FLEET_HELPER_UNIT-wm$FLEET_DISPLAY.scope"
mkdir -p "$helper_root/helper-logs"
stderr="$helper_root/helper-logs/$FLEET_HELPER_UNIT-vnc$FLEET_DISPLAY.stderr"
test ! -e "$stderr"
exec 2>"$stderr"
exec /usr/bin/x11vnc -display ":$FLEET_DISPLAY" -localhost -rfbport "$FLEET_VNC" -nopw -forever -shared -noxdamage -viewonly
