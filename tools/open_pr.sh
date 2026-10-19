#!/usr/bin/env bash
# Open the solution PR for one adapted holdout target.
# Usage: open_pr.sh INSTANCE RUN_ID
set -euo pipefail
inst="$1"; run="$2"
case "$inst" in
  holdout-x13-y13)    A='X_1^3Y_1^3'; k=-2 ;;
  holdout-p3)         A='X_2^3Y_2^3'; k=4 ;;
  holdout-x12-p-y02)  A='X_1^2X_2Y_0^2Y_2'; k=4 ;;
  holdout-p-y14)      A='X_2Y_1^4Y_2'; k=-2 ;;
  holdout-x1-y04-y1)  A='X_1Y_0^4Y_1'; k=4 ;;
  holdout-x0-y03-y12) A='X_0Y_0^3Y_1^2'; k=2 ;;
  holdout-all-six)    A='X_0X_1X_2Y_0Y_1Y_2'; k=2 ;;
  holdout-x0-x14-y0)  A='X_0X_1^4Y_0'; k=2 ;;
  holdout-x04-p)      A='X_0^4X_2Y_2'; k=2 ;;
  *) echo "unknown instance $inst" >&2; exit 1 ;;
esac
url="https://github.com/DiamondJM/hodgeHoldout/actions/runs/$run"
body=$(mktemp)
python3 "$(dirname "$0")/pr_body.py" "$inst" "$A" "$k" "$url" > "$body"
gh api -X POST repos/hodge-computer/sextics/pulls \
  -f title="Solve $inst: adapted holdout Fermat-cover and moving-conic construction" \
  -f head="DiamondJM:solve/$inst" -f base=main -F body=@"$body" \
  --jq '"\(.number) \(.html_url)"'
