#!/bin/bash
# Kept for the commands people remember: the driver is scripts/setup-sources.mjs (stateless, resumable).
#   scripts/setup-sources.sh [key...] [--status] [--retry-gave-up]
exec node "$(cd "$(dirname "$0")" && pwd)/setup-sources.mjs" "$@"
