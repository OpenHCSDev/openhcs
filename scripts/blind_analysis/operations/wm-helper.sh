#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "$1" "$2"
test "$FLEET_PARENT_RELEASED" = 1
systemctl --user is-active --quiet "$FLEET_HELPER_UNIT-x$FLEET_DISPLAY.scope"
wm=$(jq -er '.wm_config' "$helper_root/program.json")
exec /usr/bin/env DISPLAY=:$FLEET_DISPLAY /usr/bin/awesome -c "$wm"
