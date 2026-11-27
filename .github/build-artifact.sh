#!/usr/bin/env bash
# A build of the library, `.lake/build`, as an artifact of a workflow run:
# how a run packs one, and how a later run takes one. The workflows ci and
# cache-library both do this, and the artifact's form is written here once
# so that they cannot drift apart. An artifact is one file, `build.tar.zst`:
# a tar file that holds the directory `build`, which keeps the files' modes
# and the names under `.lake`.
#
# `build-artifact.sh pack DIR` writes DIR/build.tar.zst from `.lake/build`,
# for actions/upload-artifact to upload DIR. If there is no `.lake/build`,
# it says so and writes nothing.
#
# `build-artifact.sh take RUN NAME` downloads the artifact NAME of the run
# RUN of this repository and puts its build at `.lake/build`, in place of
# what is there. It needs GH_TOKEN with `actions: read`. Which run's build
# may be taken is the caller's matter: see the two workflows for what each
# of them checks first. The build is unpacked beside `.lake/build` and moved
# there only when it is whole and holds nothing but files and directories,
# so no link in it can point outside. If anything fails, the script says
# what as a warning on the run's page and exits with 1, and the caller goes
# on without the build: `.lake/build` is then as it was, or gone if it was
# the move that failed.
set -uo pipefail

warn() { echo "::warning::$1"; }

case ${1:-} in
  pack)
    dir=${2:?the directory to write build.tar.zst into}
    [ -d .lake/build ] || { echo "there is no .lake/build to pack"; exit 0; }
    mkdir -p "$dir" &&
      tar --use-compress-program 'zstd -T0' -cf "$dir/build.tar.zst" -C .lake build
    ;;
  take)
    run=${2:?the id of the run}
    name=${3:?the name of the artifact}
    dir=${RUNNER_TEMP:?}/build-artifact
    took() {
      rm -rf "$dir" && mkdir -p "$dir/unpacked" .lake || return 1
      timeout 900 gh run download "$run" --repo "$GITHUB_REPOSITORY" --name "$name" --dir "$dir" ||
        { warn "could not download the build $name of run $run"; return 1; }
      tar --use-compress-program unzstd -xf "$dir/build.tar.zst" -C "$dir/unpacked" && [ -d "$dir/unpacked/build" ] &&
        [ -z "$(find "$dir/unpacked" ! -type f ! -type d -print -quit)" ] ||
        { warn "could not unpack the build $name of run $run, or it holds something other than files and directories"; return 1; }
      if ! { rm -rf .lake/build && mv "$dir/unpacked/build" .lake/build; }; then
        rm -rf .lake/build
        warn "could not put the build $name of run $run in place"
        return 1
      fi
    }
    took
    status=$?
    rm -rf "$dir"
    [ "$status" -eq 0 ] || exit 1
    echo "took the build of run $run"
    ;;
  *)
    echo "usage: build-artifact.sh pack DIR | take RUN NAME" >&2
    exit 2
    ;;
esac
