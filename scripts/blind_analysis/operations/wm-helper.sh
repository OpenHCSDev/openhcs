#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "$1" "$2"
systemctl --user is-active --quiet "$FLEET_HELPER_UNIT-x$FLEET_DISPLAY.scope"
wm=$(jq -er '.wm_config' "$helper_root/program.json")
mkdir -p "$helper_root/helper-logs"
stderr="$helper_root/helper-logs/$FLEET_HELPER_UNIT-wm$FLEET_DISPLAY.stderr"
test ! -e "$stderr"
exec 2>"$stderr"
# DISPLAY isolates X, not session-bus names such as org.awesomewm.awful.
# Own the private bus for the WM's lifetime, including in-place WM restarts.
exec /usr/bin/dbus-run-session -- /usr/bin/env DISPLAY=:$FLEET_DISPLAY /usr/bin/awesome -c "$wm"
