#!/usr/bin/env bash
# Builds the Tau Ceti modules that the library imports, with Tau Ceti's build
# cache where it has them, for a build that has Lake's artifact cache
# (`LAKE_ARTIFACT_CACHE=true`, at `LAKE_CACHE_DIR`). The agents' jobs run it
# after `lake exe cache get` and before `lake build` (see AGENTS.md), and
# CI's setup action runs it when it finds no save of the dependencies. That
# action's comment says how Tau Ceti's cache works: `lake build` fetches
# each module that the cache has as the pinned commit would build it and
# compiles the others. Without this script, the first build after a move of
# Tau Ceti compiles them all.
#
# With `--imports`, it only prints the Tau Ceti modules that the checkout
# imports, one a line. This is the one place that reads that list.
#
# The modules land in Lake's artifact cache, which the agents' jobs of one
# kind share on a server. The script keeps a note there of the modules it
# has built, for each state of `lean-toolchain` and `lake-manifest.json`,
# and does nothing when the note has every module that the checkout imports.
# Otherwise one job at a time builds the modules that the note lacks, and
# jobs that start meanwhile wait for it and then find them in the note. That
# holds also when Tau Ceti's cache has nothing or cannot be read: one job
# compiles, and the others take its work.
#
# In CI a run may also take the modules from the bucket of Lake's cache, and
# hand over its own; see tauceti-bucket.sh, which finds the mappings
# file that this script is given as TAUCETI_BUCKET_MAPPINGS. Lake fetches
# the archives that the file names before the build, and the build takes
# from them every module whose inputs are as the file has them. (An archive
# that is not one, though its name is the hash of its content, fails that
# build and the library's after it; cache-upload.sh cannot tell, and the
# library's archives are no different in this.) With
# TAUCETI_MAPPINGS_OUT the build writes to that file the mappings of all the
# Tau Ceti modules it covered, those that were up to date or fetched as
# well as those it compiled, for which Lake packs an archive of each module
# that has none yet. The agents' jobs set neither, and the script is for
# them as it was.
#
# The script never fails: whatever goes wrong, it says so, and the build that
# follows compiles what is missing. If it is stopped, it stops its build, and
# the next run goes on from there.
set -uo pipefail
# Messages go to the script's own output, also from within a command whose
# output goes to a log.
exec 3>&1
say() { echo "tauceti-cache: $*" >&3; }
# A problem: in CI it also shows on the run's page.
warn() {
  say "$*"
  [ "${GITHUB_ACTIONS:-}" != true ] || echo "::warning::$*" >&3
}
cd "$(git rev-parse --show-toplevel)" || exit 0
# Read from the files' text.
imports() {
  git ls-files '*.lean' \
    | xargs -r sed -nE 's/^\s*(public\s+)?(meta\s+)?import\s+(all\s+)?(TauCeti\.[A-Za-z0-9_.]+).*/\4/p' \
    | sort -u
}
if [ "${1:-}" = --imports ]; then
  imports
  exit 0
fi
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
imports > "$tmp/imports.txt"
if [ ! -s "$tmp/imports.txt" ]; then
  say "the checkout imports no Tau Ceti module; nothing to do"
  exit 0
fi
notes=$LAKE_CACHE_DIR/tauceti-fetched
state=$notes/$(cat lean-toolchain lake-manifest.json | sha256sum | cut -c1-16)
mkdir -p "$notes" || exit 0
# `.modules` is the note of the modules built so far, `.mapped` says that
# Tau Ceti's cache has told which builds it has for these dependencies, and
# `.unread` is the time of the last run that asked and did not learn that.
missing() {
  sort -u "$state.modules" 2>/dev/null | comm -23 "$tmp/imports.txt" - > "$tmp/missing.txt"
  [ -s "$tmp/missing.txt" ]
}
settled() {
  missing && return 1
  say "the imported Tau Ceti modules were built here earlier; nothing to do"
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
config=$tmp/lake-cache.toml
printf '%s\n' \
  'cache.defaultService = "tauceti-public"' \
  '[[cache.service]]' \
  'name = "tauceti-public"' \
  'kind = "s3"' \
  'artifactEndpoint = "https://cache.taucetiproject.org/artifacts"' \
  'revisionEndpoint = "https://cache.taucetiproject.org/revisions"' > "$config"
# Once for these dependencies, the script asks Tau Ceti's cache which builds
# it has, for the pinned commit or the nearest of the 499 before it. The
# answer covers every module of Tau Ceti, so later runs do not ask again.
# After a run that got no answer, the runs of the next 15 minutes do not ask
# either. Lake sets no limit on a download, so each command has one here.
#
# Lake asks the cache only once it has loaded the checkout with its packages,
# and says `downloading build outputs` when it asks. A command that fails
# without that line did not get that far: something here stopped it, such as
# another Lake command that sets up `.lake/packages` at the same moment. That
# says nothing about the cache, so the script leaves no note and tries again
# every 20 seconds until 5 minutes have passed, which is 10 minutes at most,
# since the last command has its own limit. Only then does it compile from
# source, like a run that got no answer, and still without a note: the next
# run asks again.
if [ ! -e "$state.mapped" ] && [ -z "$(find "$state.unread" -mmin -15 2>/dev/null)" ]; then
  since=$SECONDS
  while true; do
    if LAKE_CONFIG=$config run timeout 5m lake cache get --service tauceti-public \
        --repo TauCetiProject/TauCeti --package TauCeti --mappings-only --max-revs=500 > "$tmp/get.log" 2>&1; then
      grep 'downloading build outputs' "$tmp/get.log" | tail -n 1
      touch "$state.mapped"
      break
    fi
    tail -n 5 "$tmp/get.log"
    if grep -q 'downloading build outputs' "$tmp/get.log"; then
      if grep -q 'no outputs found' "$tmp/get.log"; then
        warn "Tau Ceti's cache has no builds for the pinned commit or the 499 before it; the Tau Ceti modules are compiled from source"
      else
        warn "reading Tau Ceti's cache failed or took more than 5 minutes, see the lines above; the Tau Ceti modules are compiled from source"
      fi
      touch "$state.unread"
      break
    fi
    if [ $((SECONDS - since)) -ge 300 ]; then
      warn "Lake could not ask Tau Ceti's cache for 5 minutes, see the lines above; the Tau Ceti modules are compiled from source"
      break
    fi
    say "Lake did not get as far as asking Tau Ceti's cache, see the lines above; if another Lake command is setting up the packages, this passes; trying again in 20 seconds"
    run sleep 20
  done
fi
if [ -e "$state.mapped" ]; then
  export LAKE_CONFIG=$config
  with="with Tau Ceti's cache"
else
  with="from source"
fi
# The bucket's mappings come after Tau Ceti's, so that they win where both
# have a module: their archives are fetched here, at once, and Tau Ceti's
# one by one during the build. The build gets the bucket's service too, in
# case it must fetch an archive that this command did not.
if [ -s "${TAUCETI_BUCKET_MAPPINGS:-}" ]; then
  sed -n '/^\[\[cache\.service\]\]/,$p' .github/lake-config.toml >> "$config"
  export LAKE_CONFIG=$config
  if run timeout 10m lake cache get "$TAUCETI_BUCKET_MAPPINGS" --service fc-queue --package TauCeti > "$tmp/bucket.log" 2>&1; then
    say "fetched $(grep -c 'downloaded artifact' "$tmp/bucket.log") archives of Tau Ceti modules from the bucket (after ${SECONDS}s)"
    with="$with and the bucket"
  else
    tail -n 5 "$tmp/bucket.log"
    warn "fetching the Tau Ceti modules from the bucket failed or took more than 10 minutes, see the lines above; the build compiles what it lacks"
  fi
fi
out=()
if [ -n "${TAUCETI_MAPPINGS_OUT:-}" ]; then
  rm -f "$TAUCETI_MAPPINGS_OUT"
  out=(-o "$TAUCETI_MAPPINGS_OUT" --package TauCeti)
fi
limit=${TAUCETI_CACHE_BUILD_LIMIT:-60m}
mapfile -t modules < <(sed 's/^/+/' "$tmp/missing.txt")
say "building ${#modules[@]} imported Tau Ceti modules $with (after ${SECONDS}s); after a move of Tau Ceti this can take 40 minutes, and longer from source"
if LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true run timeout "$limit" lake build ${out[@]+"${out[@]}"} "${modules[@]}" > "$tmp/build.log" 2>&1; then
  { cat "$tmp/imports.txt"; cat "$state.modules" 2>/dev/null; } | sort -u > "$tmp/modules"
  cp "$tmp/modules" "$state.modules.$$" && mv "$state.modules.$$" "$state.modules"
  say "done after ${SECONDS}s: $(grep -c 'Built TauCeti\.' "$tmp/build.log") modules compiled here, the others fetched or already present"
else
  tail -n 5 "$tmp/build.log"
  # Lake writes the mappings of a failed build too, of the modules it got
  # to. In the bucket such a file would be found before fuller ones.
  [ -z "${TAUCETI_MAPPINGS_OUT:-}" ] || rm -f "$TAUCETI_MAPPINGS_OUT"
  warn "the build of the Tau Ceti modules $with failed or took more than $limit; the build that follows compiles what is missing"
fi
exit 0
