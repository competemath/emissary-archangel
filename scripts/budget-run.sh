#!/bin/bash
# budget-run.sh MINUTES WHAT THEN CMD... — CMD under `timeout -k 2m MINUTESm`, and one line saying how it ended: a ::notice:: when it stopped at its budget, an ::error::
# when it ended early with an error. Either way the step goes on (exit 0), as it did before; only a malformed MINUTES is refused (exit 2).
#
# Why (leanbridge, setup run 42427677819 and the five rounds after it, 7-8 Nov 2026): Node died at its heap limit (exit 134) in every prime build, and the step's
# `|| echo "::notice::the prime build stopped at its budget"` called each crash a budget stop. Exit 137 is no proof of the budget either: `timeout -k` ends with 137 when it
# had to kill after the budget, but so does a command the runner's out-of-memory killer took before it. So 137 counts as the budget only when the budget had run out.
set -u
min=$1 what=$2 then=$3
shift 3
[[ "$min" =~ ^[0-9]{1,4}$ ]] || { echo "::error::budget-run.sh: '$min' is not a number of minutes"; exit 2; }
unit=${BUDGET_RUN_UNIT:-m} # s in the tests, so a budget takes seconds, not minutes
[[ "$unit" == m || "$unit" == s ]] || { echo "::error::budget-run.sh: BUDGET_RUN_UNIT is m or s"; exit 2; }
secs=$min
[ "$unit" = m ] && secs=$((min * 60))
t0=$SECONDS
rc=0
timeout -k "${BUDGET_RUN_KILL_AFTER:-2m}" "${min}${unit}" "$@" || rc=$?
el=$((SECONDS - t0))
[ "$rc" -eq 0 ] && exit 0
if [ "$rc" -eq 124 ] || { [ "$rc" -eq 137 ] && [ "$el" -ge "$secs" ]; }; then
  echo "::notice::$what stopped at its budget ($min$unit); $then"
else
  echo "::error::$what ended with exit code $rc after ${el}s, not at its budget ($min$unit; 134: Node ran out of memory, 137 before the budget: killed, e.g. by the runner's out-of-memory killer; see the log above); $then"
fi
exit 0
