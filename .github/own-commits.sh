#!/usr/bin/env bash
# Prints the commits whose mappings under `r/pr/` a run of CI may read, the
# latest first, one a line: for a run for a pull request, the latest 20 of
# GitHub's list of its commits; for a run of the merge queue, the head commit
# of the pull request that it merges. For a pull request from a fork it
# prints nothing. ci.yml says, at the step that fetches from the bucket, why
# these and no others.
#
# It reads GH_TOKEN, and from the run: OWN_REPO (`true` for a branch of this
# repository), PR (the pull request's number) and QUEUE_REF (the merge
# group's ref). If GitHub does not answer, it gives a warning and prints
# nothing, and the run goes on with main's mappings alone.
set -uo pipefail
[ "${OWN_REPO:-}" = true ] || exit 0
if [ "${GITHUB_EVENT_NAME:-}" = pull_request ]; then
  timeout 60 gh api --paginate "repos/$GITHUB_REPOSITORY/pulls/${PR:-}/commits" --jq '.[].sha' | tail -n 20 | tac ||
    echo "::warning::could not ask GitHub for the commits of pull request ${PR:-}" >&2
elif [[ ${QUEUE_REF:-} =~ ^refs/heads/gh-readonly-queue/main/pr-([0-9]+)-[0-9a-f]{40}$ ]]; then
  timeout 60 gh api "repos/$GITHUB_REPOSITORY/pulls/${BASH_REMATCH[1]}" --jq '.head.sha' ||
    echo "::warning::could not ask GitHub for the head commit of pull request ${BASH_REMATCH[1]}" >&2
fi
exit 0
