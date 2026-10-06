#!/bin/bash
# Controlled existing-owner contract; no real programme/runtime is consulted.
FLEET_ROOT=${1:?root}
FLEET_SLOT=${2:?declared test leaf}
FLEET_WORKSPACE="$FLEET_ROOT/$FLEET_SLOT/author-workspace"
FLEET_OPERATIONS="$FLEET_ROOT/operations"
fleet_require_writer_release() { printf 'writer\n' >> "$FLEET_ROOT/calls"; }
