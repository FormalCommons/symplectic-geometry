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
# on a server. So when several jobs start together, one fetches and the
# others wait for it, and a job that finds the note of an earlier fetch, for
# the same commit of Tau Ceti and the same list of imported modules, does
# nothing. The list is read as the setup action reads it.
#
# The script never fails. Whatever goes wrong, it says so, and the build
# that follows compiles what is missing.
set -uo pipefail
say() { echo "tauceti-cache: $*"; }
cd "$(git rev-parse --show-toplevel)" || exit 0
if [ "${LAKE_ARTIFACT_CACHE:-}" != true ] || [ -z "${LAKE_CACHE_DIR:-}" ]; then
  say "no Lake artifact cache here (LAKE_ARTIFACT_CACHE, LAKE_CACHE_DIR); nothing to do"
  exit 0
fi
tmp=$(mktemp -d) || exit 0
trap 'rm -rf "$tmp"' EXIT
pin=$(sed -nE 's/^rev = "([0-9a-f]{40})".*/\1/p' lakefile.toml)
git ls-files '*.lean' \
  | xargs -r sed -nE 's/^\s*(public\s+)?import\s+(TauCeti\.[A-Za-z0-9_.]+).*/\2/p' \
  | sort -u > "$tmp/imports.txt"
mapfile -t modules < <(sed 's/^/+/' "$tmp/imports.txt")
if [ -z "$pin" ] || [ ${#modules[@]} -eq 0 ]; then
  say "no rev of Tau Ceti's in lakefile.toml, or no import of Tau Ceti; nothing to do"
  exit 0
fi
notes=$LAKE_CACHE_DIR/tauceti-fetched
note=$notes/$pin-$(sha256sum < "$tmp/imports.txt" | cut -c1-16)
mkdir -p "$notes" || exit 0
if [ -e "$note" ]; then
  say "fetched earlier on this server for Tau Ceti ${pin:0:12} and these imports; nothing to do"
  exit 0
fi
# One job at a time. The wait is shorter than the fetch below may take, so
# that a job does not spend its whole time waiting.
exec 9> "$notes/lock" || exit 0
say "waiting for other jobs that fetch, if there are any"
if ! flock -w 2700 9; then
  say "another job has fetched for 45 minutes; going on without"
  exit 0
fi
if [ -e "$note" ]; then
  say "another job fetched meanwhile; nothing to do"
  exit 0
fi
export LAKE_CONFIG=$tmp/lake-cache.toml
printf '%s\n' \
  'cache.defaultService = "tauceti-public"' \
  '[[cache.service]]' \
  'name = "tauceti-public"' \
  'kind = "s3"' \
  'artifactEndpoint = "https://cache.taucetiproject.org/artifacts"' \
  'revisionEndpoint = "https://cache.taucetiproject.org/revisions"' > "$LAKE_CONFIG"
# Lake sets no limit on a download, so each command has one here.
if timeout 10m lake cache get --service tauceti-public --repo TauCetiProject/TauCeti \
    --package TauCeti --mappings-only --max-revs=500 > "$tmp/get.log" 2>&1; then
  grep 'downloading build outputs' "$tmp/get.log" | tail -n 1 || true
  say "building ${#modules[@]} imported Tau Ceti modules with Tau Ceti's cache; after a move this can take 40 minutes"
  if LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true timeout 60m lake build "${modules[@]}" > "$tmp/build.log" 2>&1; then
    say "done: $(grep -c 'Built TauCeti\.' "$tmp/build.log") modules compiled here, the others fetched or already present"
    touch "$note"
  else
    tail -n 5 "$tmp/build.log"
    say "the build from Tau Ceti's cache failed or took too long; the build that follows compiles what is missing"
  fi
else
  tail -n 5 "$tmp/get.log"
  if grep -q 'no outputs found' "$tmp/get.log"; then
    say "Tau Ceti's cache has no builds for the pinned commit or the 499 before it; the build that follows compiles the Tau Ceti modules"
    touch "$note"
  else
    say "reading Tau Ceti's cache failed or took longer than 10 minutes, see the lines above; the build that follows compiles the Tau Ceti modules"
  fi
fi
exit 0
