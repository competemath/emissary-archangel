#!/bin/bash
# dispatch.sh RUNS.txt MAX KEY... — dispatch bump-library.yml for each key, never more than MAX of ITS runs unfinished at once;
# appends `key run_id` to RUNS.txt as each starts. Extra workflow inputs through BUMP_INPUTS (e.g. "-f chain=auto").
R=competemath/emissary-archangel
runs=$1; max=$2; shift 2
active() { local n=0; while read -r _ id; do [ "$(gh run view "$id" -R $R --json status -q .status 2>/dev/null)" = completed ] || n=$((n+1)); done < "$runs"; echo $n; }
touch "$runs"
for key in "$@"; do
  while [ "$(active)" -ge "$max" ]; do sleep 60; done
  before=$(gh run list -R $R --workflow bump-library.yml --limit 1 --json databaseId -q '.[0].databaseId')
  gh workflow run bump-library.yml -R $R --ref main -f key="$key" $BUMP_INPUTS >/dev/null 2>&1 || { echo "$key: dispatch failed"; continue; }
  id=""
  for _ in $(seq 1 30); do
    id=$(gh run list -R $R --workflow bump-library.yml --limit 5 --json databaseId,displayTitle -q ".[]|select(.databaseId>$before)|.databaseId" | tail -1)
    [ -n "$id" ] && break; sleep 4
  done
  echo "$key $id" >> "$runs"; echo "dispatched $key $id"
done
