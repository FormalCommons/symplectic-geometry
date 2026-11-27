#!/usr/bin/env bash
# The Tau Ceti modules in the bucket of Lake's cache, for the runs of CI that
# find no save of the dependencies: the runs of a move of Tau Ceti, and every
# run in the hour or so between a move's merge and main's save. Such a run
# compiles the Tau Ceti modules that Tau Ceti's own cache does not have as
# the pinned commit builds them, which after the move to 0aaa80fd were 2,047
# modules and an hour on a runner, in each run. With this script a run takes
# from the bucket the modules that an earlier run handed over, and hands
# over its own: the mappings of all the Tau Ceti modules that its build
# covered, those it compiled and those it fetched, and the archives that
# the bucket's file does not name.
#
#   tauceti-bucket.sh find DIR
#   tauceti-bucket.sh stage MAPPINGS DIR OUT
#
# `find` looks in the bucket for a mappings file of Tau Ceti modules that
# this run may read, and writes it to DIR/mappings.jsonl, and to DIR/from a
# line `pr <commit>` or `queue <commit>` that says where it was. It only
# downloads that file. tauceti-cache.sh then has Lake fetch the archives
# (TAUCETI_BUCKET_MAPPINGS) and writes the mappings of all the Tau Ceti
# modules that its build covered (TAUCETI_MAPPINGS_OUT).
#
# A run reads one file: main's latest for these dependencies under
# `r/queue/`, or without one the latest of its own commits under `r/pr/`
# (own-commits.sh, which says whose those are). The file of a commit is
# `<commit>.tauceti.jsonl`, beside the library's `<commit>.jsonl`, which is
# the name Lake itself reads. main's are looked for at the commit that is
# checked out and the 99 before it, as `git rev-list` orders them; in a pull
# request's merge those are the branch's commits and main's, mixed. A commit
# whose lean-toolchain or lake-manifest.json differs from those checked out
# is passed over: its file was written for other dependencies and would
# cover nothing here. main's come first, so that where main has a file a
# pull request's own never stands in for it.
#
# What this trusts. Unlike the library's modules, Tau Ceti's do not change
# with main, so a run of the merge queue that reads the file of the pull
# request it merges compiles none of these modules itself, and what it
# writes becomes main's file, which the runs after it read. That is the case
# for a move of Tau Ceti, where main has no file yet. What stands behind
# those modules is the review's own build of the pull request and main's
# save of the dependencies, neither of which reads the bucket; until main
# has that save, the runs of CI take the modules on the word of the move's
# own run.
#
# The search gives up after two minutes, and the run goes on without the
# bucket.
#
# `stage` makes OUT, the directory that CI hands to the workflow
# cache-upload as the artifact `lake-cache-tauceti`: OUT/staged, with
# MAPPINGS as outputs.jsonl and the archives that MAPPINGS names and the
# file that `find` found does not, and OUT/from, a copy of DIR/from. The
# archives that the found file names are in the bucket already, since
# mappings are uploaded after their archives and nothing there is deleted.
# cache-upload reads OUT/from only to fetch that file from the bucket
# itself, so that it need not ask about each of those archives.
#
# The workflow cache-dependencies, which makes main's save of the
# dependencies, does not use this script: that save is built from Tau Ceti's
# source and Tau Ceti's own cache alone.
#
# `find` never fails: whatever goes wrong, it says so, and the run goes on
# as without the bucket. `stage` fails when it has nothing to hand over; the
# step that runs it lets the run go on, and only the bucket goes without.
set -uo pipefail
say() { echo "tauceti-bucket: $*"; }
cd "$(git rev-parse --show-toplevel)" || exit 0
here=.github

find_mappings() {
  local dir=$1 toolchain pr queue c
  mkdir -p "$dir" || return 0
  rm -f "$dir/mappings.jsonl" "$dir/from"
  toolchain=$(cat lean-toolchain) || return 0
  pr=$(python3 -I "$here/lake-cache-address.py" fc-pr "$toolchain" | sed -n 2p) && [ -n "$pr" ] &&
    queue=$(python3 -I "$here/lake-cache-address.py" fc-queue "$toolchain" | sed -n 2p) && [ -n "$queue" ] ||
    { say "no address for the mappings; nothing taken from the bucket"; return 0; }
  # take KIND ADDRESS COMMIT: downloads the commit's file if the bucket has it.
  take() {
    [[ $3 =~ ^[0-9a-f]{40}$ ]] || return 1
    curl -q -sf --connect-timeout 5 --max-time 15 -o "$dir/mappings.jsonl" "$2/$3.tauceti.jsonl" ||
      { rm -f "$dir/mappings.jsonl"; return 1; }
    echo "$1 $3" > "$dir/from"
    say "the bucket has Tau Ceti modules for the commit $3 (r/$1): $(($(wc -l < "$dir/mappings.jsonl") - 1)) mappings"
  }
  SECONDS=0
  late() {
    [ "$SECONDS" -lt 120 ] && return 1
    say "the search of the bucket took more than two minutes; going on without it"
  }
  # It must go on after a commit with other dependencies: in a pull
  # request's merge, the branch's commits from before a move stand among
  # main's.
  for c in $(git rev-list -n 100 HEAD 2>/dev/null); do
    late && return 0
    git diff --quiet "$c" HEAD -- lean-toolchain lake-manifest.json 2>/dev/null || continue
    take queue "$queue" "$c" && return 0
  done
  for c in $("$here/own-commits.sh"); do
    late && return 0
    take pr "$pr" "$c" && return 0
  done
  say "the bucket has no Tau Ceti modules for these dependencies among main's commits or this run's own"
}

stage() {
  local mappings=$1 dir=$2 out=$3 new
  [ -s "$mappings" ] || { say "the build of the Tau Ceti modules wrote no mappings; nothing to hand over"; return 1; }
  # A run that found nothing when it started looks again now, an hour or
  # more later: an earlier run's modules have often reached the bucket
  # meanwhile. Then this run hands over only its mappings and what that
  # file lacks, and cache-upload does not ask the bucket about some
  # thousands of archives, as every run of a move that started together
  # would.
  [ -s "$dir/from" ] || find_mappings "$dir"
  rm -rf "$out"
  mkdir -p "$out/staged" || return 1
  new=$(mktemp) || return 1
  # The first line is the format's date; the others are the mappings.
  head -n 1 "$mappings" > "$new"
  if [ -s "$dir/mappings.jsonl" ]; then
    tail -n +2 "$mappings" | grep -vxFf <(tail -n +2 "$dir/mappings.jsonl") >> "$new"
  else
    tail -n +2 "$mappings" >> "$new"
  fi
  say "$(($(wc -l < "$mappings") - 1)) mappings, of which $(($(wc -l < "$new") - 1)) are not in a file from the bucket"
  if [ "$(wc -l < "$new")" -gt 1 ]; then
    lake cache stage "$new" "$out/staged" || { rm -f "$new"; say "could not stage the archives"; return 1; }
  fi
  rm -f "$new"
  cp "$mappings" "$out/staged/outputs.jsonl" || return 1
  [ ! -s "$dir/from" ] || cp "$dir/from" "$out/from"
}

case ${1:-} in
  find) find_mappings "${2:?the directory for what is found}" ;;
  stage) stage "${2:?the mappings file}" "${3:?the directory of find}" "${4:?the directory to hand over}" || exit 1 ;;
  *) echo "usage: $0 find DIR | stage MAPPINGS DIR OUT" >&2; exit 2 ;;
esac
exit 0
