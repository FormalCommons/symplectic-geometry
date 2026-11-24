#!/usr/bin/env bash
# Takes the Tau Ceti modules that the library imports from Tau Ceti's build
# cache, for a build in a container that has Lake's artifact cache
# (`LAKE_ARTIFACT_CACHE=true`, at `LAKE_CACHE_DIR`), as the agents' jobs
# have. Run it after `lake exe cache get` and before `lake build`; see
# AGENTS.md.
#
# It does what CI's setup action does when it finds no save of the
# dependencies, and that action's comment says how Tau Ceti's cache works:
# `lake build` fetches each module that the cache has as the pinned commit
# would build it and compiles the others. Without this script, the first
# build after a move of Tau Ceti compiles them all.
#
# The modules land in Lake's artifact cache, which the jobs of one kind share
# on a server. The script keeps a note there of the modules it has built,
# for each state of `lean-toolchain` and `lake-manifest.json`, and does
# nothing when the note has every module that the checkout imports. The
# list of those is read as the setup action reads it. Otherwise one job at a
# time builds the modules that the note lacks, and jobs that start meanwhile
# wait for it and then find them in the note.
#
# The script never fails: whatever goes wrong, it says so, and the build that
# follows compiles what is missing. If it is stopped, it stops its build, and
# the next run goes on from there.
set -uo pipefail
# Messages go to the script's own output, also from within a command whose
# output goes to a log.
exec 3>&1
say() { echo "tauceti-cache: $*" >&3; }
cd "$(git rev-parse --show-toplevel)" || exit 0
if [ "${LAKE_ARTIFACT_CACHE:-}" != true ] || [ -z "${LAKE_CACHE_DIR:-}" ]; then
  say "no Lake artifact cache here (LAKE_ARTIFACT_CACHE, LAKE_CACHE_DIR); nothing to do"
  exit 0
fi
tmp=$(mktemp -d) || exit 0
child=
# shellcheck disable=SC2329  # called by the trap below
stop() {
  # `timeout` passes the signal on to Lake and to what Lake started.
  [ -n "$child" ] && kill -TERM "$child" 2>/dev/null && wait "$child" 2>/dev/null
  say "stopped; run it again to go on"
  exit 0
}
trap 'rm -rf "$tmp"' EXIT
trap stop TERM INT HUP
# Runs a command so that a signal to this script stops it too.
run() {
  "$@" &
  child=$!
  wait "$child"
  local status=$?
  child=
  return "$status"
}
git ls-files '*.lean' \
  | xargs -r sed -nE 's/^\s*(public\s+)?import\s+(TauCeti\.[A-Za-z0-9_.]+).*/\2/p' \
  | sort -u > "$tmp/imports.txt"
if [ ! -s "$tmp/imports.txt" ]; then
  say "the checkout imports no Tau Ceti module; nothing to do"
  exit 0
fi
notes=$LAKE_CACHE_DIR/tauceti-fetched
state=$notes/$(cat lean-toolchain lake-manifest.json | sha256sum | cut -c1-16)
mkdir -p "$notes" || exit 0
# The note has the modules built so far, `.none` says that Tau Ceti's cache
# had nothing for these dependencies, and `.failed` is the time of the last
# run that could not read Tau Ceti's cache.
missing() {
  sort -u "$state.modules" 2>/dev/null | comm -23 "$tmp/imports.txt" - > "$tmp/missing.txt"
  [ -s "$tmp/missing.txt" ]
}
settled() {
  if [ -e "$state.none" ]; then
    say "Tau Ceti's cache had no builds for these dependencies; nothing to do"
  elif ! missing; then
    say "the imported Tau Ceti modules were built here earlier; nothing to do"
  elif [ -n "$(find "$state.failed" -mmin -15 2>/dev/null)" ]; then
    say "Tau Ceti's cache could not be read in the last 15 minutes; going on without"
  else
    return 1
  fi
}
settled && exit 0
# One job at a time for these dependencies. The wait is limited, so that a
# job does not spend all its time here.
exec 9> "$state.lock" || exit 0
if ! flock -n 9; then
  say "another job builds the Tau Ceti modules; waiting for it, 45 minutes at most"
  if ! run flock -w 2700 9; then
    say "it is not done after 45 minutes; going on without"
    exit 0
  fi
  settled && exit 0
fi
export LAKE_CONFIG=$tmp/lake-cache.toml
printf '%s\n' \
  'cache.defaultService = "tauceti-public"' \
  '[[cache.service]]' \
  'name = "tauceti-public"' \
  'kind = "s3"' \
  'artifactEndpoint = "https://cache.taucetiproject.org/artifacts"' \
  'revisionEndpoint = "https://cache.taucetiproject.org/revisions"' > "$LAKE_CONFIG"
# The first run for these dependencies asks Tau Ceti's cache which builds it
# has, for the pinned commit or the nearest of the 499 before it. That covers
# every module of Tau Ceti, so later runs do not ask again. Lake sets no
# limit on a download, so each command has one here.
if [ ! -e "$state.modules" ]; then
  if run timeout 5m lake cache get --service tauceti-public --repo TauCetiProject/TauCeti \
      --package TauCeti --mappings-only --max-revs=500 > "$tmp/get.log" 2>&1; then
    grep 'downloading build outputs' "$tmp/get.log" | tail -n 1
  elif grep -q 'no outputs found' "$tmp/get.log"; then
    tail -n 3 "$tmp/get.log"
    say "Tau Ceti's cache has no builds for the pinned commit or the 499 before it; the build that follows compiles the Tau Ceti modules"
    touch "$state.none"
    exit 0
  else
    tail -n 5 "$tmp/get.log"
    say "reading Tau Ceti's cache failed or took more than 5 minutes; the build that follows compiles the Tau Ceti modules"
    touch "$state.failed"
    exit 0
  fi
fi
mapfile -t modules < <(sed 's/^/+/' "$tmp/missing.txt")
say "building ${#modules[@]} imported Tau Ceti modules with Tau Ceti's cache (after ${SECONDS}s); after a move of Tau Ceti this can take 40 minutes"
if LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true run timeout 60m lake build "${modules[@]}" > "$tmp/build.log" 2>&1; then
  { cat "$tmp/imports.txt"; cat "$state.modules" 2>/dev/null; } | sort -u > "$tmp/modules"
  cp "$tmp/modules" "$state.modules.$$" && mv "$state.modules.$$" "$state.modules"
  say "done after ${SECONDS}s: $(grep -c 'Built TauCeti\.' "$tmp/build.log") modules compiled here, the others fetched or already present"
else
  tail -n 5 "$tmp/build.log"
  say "the build with Tau Ceti's cache failed or took more than 60 minutes; the build that follows compiles what is missing"
fi
exit 0
