#!/usr/bin/env bash
# Given a lean-check run id: confirm it passed both checks, confirm the fork branch matches the
# compiled proposal folder, then open the PR through the open-pr workflow and print the outcome.
set -euo pipefail
run="$1"
t=$(gh api repos/DiamondJM/hodgeholdout/issues --jq ".[] | select(.title|contains(\"$run\")) | .title")
echo "$t"
inst=$(echo "$t" | awk '{print $2}')
echo "$t" | grep -q "compile rc=0 official rc=0" || { echo "run $run did not pass both checks"; exit 1; }
cd /home/user/sextics && git checkout -q "solve/$inst"
if diff -rq "data/$inst" "/home/user/hodgeholdout/proposals/$inst" | grep -v "Only in data/"; then echo "branch differs from proposals"; git checkout -q main; exit 1; fi
git checkout -q main
gh api -X POST repos/DiamondJM/hodgeholdout/actions/workflows/open-pr.yml/dispatches -f ref=main -f "inputs[instance]=$inst" -f "inputs[run_id]=$run" >/dev/null && echo "dispatched open-pr for $inst"
sleep 70
gh api repos/DiamondJM/hodgeholdout/issues --jq ".[] | select(.title|startswith(\"open-pr $inst\")) | \"\(.title)\n\(.body)\""
