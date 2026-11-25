#!/usr/bin/env bash
# Gives the runs of one cache workflow on one branch their turns, so that
# two of them do not build the same thing at once. The workflows do not use
# GitHub's `concurrency` for this: it cancels a job that waits when a later
# one comes to wait, and a cancelled job marks its commit as failed.
#
# An earlier run, here, is a run of the same workflow on the same branch
# with a smaller id: GitHub numbers the runs as it creates them.
#
# `cache-turn.sh wait` is for a job that follows the branch. It waits until
# no earlier run is still going, and then writes `go=true` to the step's
# outputs. If the branch moves on from the run's commit first, the script
# writes `go=false`, and the job has nothing to do: the push that moved the
# branch began a run of its own. So of the runs that wait, only the latest
# stays. On a ref that is not a branch, the script does not look for a move.
#
# `cache-turn.sh once` does not wait and does not look at the branch. It
# writes `go=true` if no earlier run is still going, and `go=false`
# otherwise.
#
# The script cannot tell whether an earlier run is going when GitHub does
# not answer, and when few are left of the requests that GitHub allows the
# repository's workflows in an hour, which CI's setup check needs too. Then
# `once` writes `go=false`: the next run asks again. `wait` asks again after
# a pause, and still ends when the branch moves, which it learns from git
# and not from a request. If it has had no answer for 75 minutes, which is
# longer than the hour after which GitHub allows requests again, it writes
# `go=true`: two runs that build at once waste work, but each save is whole,
# and where two save under one name, GitHub keeps the first.
#
# An earlier run that began more than 4 hours ago counts as ended, with a
# warning. Each job of the cache workflows has a limit below that, so such a
# run is stuck at GitHub, and without this rule no later run would build.
# The script also does not see an earlier run that is no longer among the
# workflow's latest 100 on the branch.
set -euo pipefail
mode=${1:-}
[ "$mode" = wait ] || [ "$mode" = once ] || { echo "usage: cache-turn.sh wait|once" >&2; exit 2; }
# The workflow's file, which names the workflow to GitHub.
workflow=${GITHUB_WORKFLOW_REF%%@*}
workflow=${workflow##*/}
# The requests of the hour that the script leaves to the other workflows.
reserve=250
# The seconds from one look to the next.
pause=${CACHE_TURN_PAUSE:-30}
# The seconds after which a run that has not ended counts as stuck.
stuck=${CACHE_TURN_STUCK:-14400}
# The seconds that `wait` goes without an answer before it lets the job go on.
patience=${CACHE_TURN_PATIENCE:-4500}
# The seconds that one question to GitHub may take.
limit=60

# Sets `going` to the number of earlier runs that have not ended, and fails
# if it cannot tell. Asking how many requests are left is not itself counted
# as a request. It says each thing in the log once.
told='' few='' warned=''
earlier() {
  local rate left answer old
  rate=$(timeout "$limit" gh api rate_limit --jq '.resources.core | "\(.remaining) \(.limit)"') || return 1
  left=${rate%% *}
  [[ $left =~ ^[0-9]+$ ]] || return 1
  if [ -z "$told" ]; then
    echo "$left of the ${rate##* } requests that GitHub allows the workflows in an hour are left"
    told=1
  fi
  if [ "$left" -lt "$reserve" ]; then
    [ -n "$few" ] || echo "::notice::$left requests to GitHub are left to the workflows for this hour, so this run does not ask for earlier runs"
    few=1
    return 1
  fi
  answer=$(timeout "$limit" gh api -X GET "repos/$GITHUB_REPOSITORY/actions/workflows/$workflow/runs" \
    -f branch="$GITHUB_REF_NAME" -F per_page=100 \
    --jq "[.workflow_runs[] | select(.id < $GITHUB_RUN_ID and .status != \"completed\")
           | ((.run_started_at // .created_at) | fromdateiso8601) > now - $stuck]
          | \"\(map(select(.)) | length) \(map(select(. | not)) | length)\"") || return 1
  going=${answer%% *}
  old=${answer##* }
  [[ $going =~ ^[0-9]+$ ]] && [[ $old =~ ^[0-9]+$ ]] || return 1
  if [ "$old" -gt 0 ] && [ -z "$warned" ]; then
    echo "::warning::$old earlier run(s) of $workflow began more than $(( stuck / 60 )) minutes ago and have not ended. This run does not wait for them. Cancel them in the list of the workflow's runs."
    warned=1
  fi
}

go=true
waited=
silent=
while :; do
  if [ "$mode" = wait ] && [[ $GITHUB_REF == refs/heads/* ]]; then
    # Without an answer, the branch counts as where it was.
    head=$(timeout "$limit" git ls-remote origin "$GITHUB_REF" | cut -f1) || head=
    if [ -n "$head" ] && [ "$head" != "$GITHUB_SHA" ]; then
      echo "$GITHUB_REF_NAME has moved on to $head, so this run has nothing to do"
      go=false
      break
    fi
  fi
  if earlier; then
    silent=
    [ "$going" -gt 0 ] || break
    if [ "$mode" = once ]; then
      echo "an earlier run of $workflow is still going, so this run has nothing to do"
      go=false
      break
    fi
    [ -n "$waited" ] || echo "waiting for an earlier run of $workflow to end"
    waited=1
  elif [ "$mode" = once ]; then
    echo "could not ask GitHub for earlier runs, so this run does nothing, and the next one asks again"
    go=false
    break
  else
    if [ -z "$silent" ]; then
      echo "could not ask GitHub for earlier runs, so this run asks again until it can"
      silent=$SECONDS
    elif [ $(( SECONDS - silent )) -ge "$patience" ]; then
      echo "::warning::GitHub has not said for $(( patience / 60 )) minutes whether an earlier run of $workflow is going, so this run goes on"
      break
    fi
  fi
  sleep "$pause"
done
echo "go=$go" >> "$GITHUB_OUTPUT"
