#!/usr/bin/env bash
# Uploads a staged build to the bucket of Lake's cache. Only the workflow
# cache-upload runs this, from main's copy, with the bucket's key.
#
#   cache-upload.sh DIR ARTIFACTS MAPPINGS [KNOWN]
#
# DIR is what a run of CI staged with `lake cache stage`: the build archives,
# each named `<hash>.ltar`, and `outputs.jsonl`, the mappings. For the Tau
# Ceti modules (tauceti-bucket.sh) it holds only the archives that the run
# did not find in the bucket. ARTIFACTS is
# the address under which the archives go, as `<hash>.art`. MAPPINGS is the
# whole address of the mappings file. KNOWN, if given, is a mappings file that
# the bucket holds under `r/`. The key comes on standard input, as the
# line `user = "<access key>:<secret>"` of a curl config, so that it is in no
# argument list.
#
# An archive that the mappings name is in one of three states. KNOWN names
# it: then it is in the bucket, since a mappings file is uploaded after its
# archives and nothing in the bucket is deleted. Or it is staged: then it is
# sent, and the bucket refuses it if it has it (see below). Or neither: then
# the bucket is asked, and must have it.
#
# So the bucket is not asked about an archive that can be sent. It was,
# until a run handed over the Tau Ceti modules of a move for the first time:
# 5,829 archives, about each of which the script first asked and which it
# would then have sent, and it had not finished asking when its ten minutes
# on a runner were over. Why is not known: the same questions take a minute
# from a machine as far from the bucket as a runner, runners ask about a
# hundred archives in a second or two, and the script printed nothing while
# it asked. When Hetzner has too many requests it holds them for five
# seconds and answers 503, and curl tries them again without a word; the
# script now counts those.
#
# Without KNOWN, every staged archive is sent, bodies and all. For the Tau
# Ceti modules of a move that is the first upload, and the bucket has none.
# For the library it is rare, and the bucket then has most and refuses
# them. Several uploads without KNOWN at once are more than Hetzner
# answers: when each asked about 1,500 archives, it sent 503, curl tried
# again, and uploads stood for 20 minutes on runners that builds were
# waiting for. Sending is no lighter than asking.
#
# If the bucket should ever lose an archive that KNOWN names, a commit's
# mappings name an archive that is not there, and a build compiles that
# module. If objects are ever made to expire, this must be thought through
# again.
#
# The script says after each part how many seconds have passed since its
# start, and how many requests curl made more than once, so that a slow
# upload shows where its time went.
#
# DIR comes from a build, which ran the code of a pull request, so nothing in
# it is trusted and nothing from it is run:
#
# - Every file must be a regular file with the name of an archive, and its
#   content must hash to its name (lake-hash.py). So an archive in the bucket
#   is what its name says, and Lake, which checks the same on download, never
#   meets one that it must refuse.
# - The mappings must be lines of the form that Lake writes, and every
#   archive that they name must be in DIR or already in the bucket.
# - Nothing in the bucket is replaced. Every upload carries
#   `If-None-Match: *`, which makes the bucket refuse it (412) if the name
#   is taken, also when two uploads race. A commit's mappings that are there
#   already stay as they are.
# - The mappings go last, so that a commit's mappings never name an archive
#   that is not there.
#
# If anything is wrong the script says what and exits with 1, and nothing or
# only archives have been uploaded: archives without mappings do no harm.
#
# The two content types are Lake's own, `artifactContentType` and
# `mapContentType` in its Lake/Config/Cache.lean.
set -euo pipefail

dir=${1:?the staged directory} artifacts=${2:?the address of the archives} mappings=${3:?the address of the mappings}
known=${4:-}
here=$(cd "$(dirname "$0")" && pwd)
key=$(cat)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
fail() { echo "::error::$1"; exit 1; }

[ -f "$dir/outputs.jsonl" ] && [ ! -L "$dir/outputs.jsonl" ] || fail "the staged build has no mappings file"

# The files: only archives beside the mappings, each named by its hash.
shopt -s nullglob dotglob
files=()
for f in "$dir"/*; do
  name=${f##*/}
  [ "$name" = outputs.jsonl ] && continue
  [[ $name =~ ^[0-9a-f]{16}\.ltar$ ]] && [ -f "$f" ] && [ ! -L "$f" ] || fail "the staged build holds something that is not an archive: $name"
  files+=("$f")
done
if [ ${#files[@]} -gt 0 ]; then
  printf '%s\0' "${files[@]}" | xargs -0 python3 -I "$here/lake-hash.py" || fail "an archive's content does not hash to its name"
fi

# The mappings: a first line with the format's date, then pairs of an input
# hash and an archive.
jq -e -s '
  (.[0] | type == "string") and
  all(.[1:][]; type == "array" and length == 2 and
    (.[0] | type == "string" and test("^[0-9a-f]{16}$")) and
    (.[1] | type == "string" and length == 21 and test("^[0-9a-f]{16}\\.ltar$")))' "$dir/outputs.jsonl" >/dev/null ||
  fail "the mappings file is not of the form that Lake writes for packed archives"
jq -r -s '.[1:][] | .[1] | sub("\\.ltar$"; "")' "$dir/outputs.jsonl" | sort -u > "$work/named"

# The archives that KNOWN names are in the bucket. A KNOWN that is not of
# the form of a mappings file counts for nothing.
: > "$work/known"
if [ -n "$known" ] && [ -f "$known" ]; then
  jq -r -s 'if (.[0] | type == "string") and all(.[1:][]; type == "array" and length == 2 and (.[1] | type == "string" and test("^[0-9a-f]{16}\\.ltar$")))
    then .[1:][] | .[1] | sub("\\.ltar$"; "") else empty end' "$known" 2>/dev/null | sort -u > "$work/known" || : > "$work/known"
fi
echo "checked ${#files[@]} staged archives and the mappings after ${SECONDS}s"
# What KNOWN does not name: the staged ones are sent, and the bucket is
# asked about the others, without a key.
if [ ${#files[@]} -gt 0 ]; then
  printf '%s\n' "${files[@]##*/}" | sed 's/\.ltar$//' | sort -u > "$work/staged"
else
  : > "$work/staged"
fi
comm -23 "$work/named" "$work/known" > "$work/rest"
comm -12 "$work/rest" "$work/staged" > "$work/send"
comm -23 "$work/rest" "$work/staged" > "$work/ask"
while read -r hash; do
  printf 'url = "%s/%s.art"\noutput = "/dev/null"\n' "$artifacts" "$hash"
done < "$work/ask" > "$work/head.cfg"
if [ -s "$work/head.cfg" ]; then
  curl -q -sS -Z --parallel-max 32 --retry 3 --retry-all-errors --retry-max-time 60 --max-time 30 -I \
    -w '%{http_code} %{url_effective} %{num_retries}\n' -K "$work/head.cfg" > "$work/head.out" || fail "could not ask the bucket which archives it has"
fi
: >> "$work/head.out"
[ "$(wc -l < "$work/head.out")" -eq "$(wc -l < "$work/ask")" ] ||
  fail "curl answered for $(wc -l < "$work/head.out") of the $(wc -l < "$work/ask") archives asked about"
while read -r code url _; do
  hash=${url##*/}; hash=${hash%.art}
  case $code in
    200) ;;
    404) fail "the mappings name the archive $hash, which is neither staged nor in the bucket" ;;
    *) fail "the bucket answered $code for an archive" ;;
  esac
done < "$work/head.out"
send=$(wc -l < "$work/send")
echo "archives named: $(wc -l < "$work/named"), known to be in the bucket: $(comm -12 "$work/named" "$work/known" | wc -l), asked about and there: $(wc -l < "$work/ask") ($(awk '$3 > 0' "$work/head.out" | wc -l) asked more than once), to send: $send (after ${SECONDS}s)"

# Hetzner answers 503 to many uploads at once; curl tries those again, and a
# broken connection too. An answer such as 403 or 412 is no error to curl
# without `--fail`, so it is not tried again. 412 means that the bucket has
# the archive: from an earlier run, from another upload meanwhile, or from
# this upload's own first try. Each is as good as uploaded. Each upload's
# answer goes to /dev/null by a line of its own in
# the config: one `-o` on the command line serves only the first, and the
# text of a 412 among the status codes failed uploads that had lost a race
# for an archive, as two runs of one batch of the merge queue do. The tries are few and bounded in time: a run's work that does
# not reach the bucket costs a later build some compiling, and an upload
# that hangs costs a runner that a build is waiting for. Two of the first
# uploads hung for the job's whole 20 minutes.
#
# The archives go a thousand at a time, and the script says so after each
# thousand.
: > "$work/put.out"
split -l 1000 -d -a 4 "$work/send" "$work/send."
sent=0
for part in "$work"/send.[0-9]*; do
  [ -s "$part" ] || continue
  { printf '%s\n' "$key"
    while read -r hash; do
      printf 'upload-file = "%s"\nurl = "%s/%s.art"\noutput = "/dev/null"\n' "$dir/$hash.ltar" "$artifacts" "$hash"
    done < "$part"; } |
    curl -q -sS -Z --parallel-max 16 --retry 4 --retry-all-errors --retry-max-time 90 --max-time 120 -w '%{http_code} %{num_retries}\n' \
      --aws-sigv4 aws:amz:auto:s3 -H 'Content-Type: application/vnd.reservoir.artifact' \
      -H 'If-None-Match: *' -K - >> "$work/put.out" || fail "could not upload the archives"
  if grep -qvE '^(200|412) ' "$work/put.out"; then
    fail "the bucket answered $(grep -vE '^(200|412) ' "$work/put.out" | cut -d ' ' -f 1 | sort | uniq -c | tr -s ' \n' ' ') to uploads of archives"
  fi
  sent=$((sent + $(wc -l < "$part")))
  [ "$(wc -l < "$work/put.out")" -eq "$sent" ] || fail "curl answered for $(wc -l < "$work/put.out") of the $sent archives sent"
  echo "sent $sent of $send archives after ${SECONDS}s, $(awk '$2 > 0' "$work/put.out" | wc -l) of them more than once"
done
[ "$send" -eq 0 ] ||
  echo "of the $send archives sent, the bucket took $(grep -c '^200 ' "$work/put.out") and had $(grep -c '^412 ' "$work/put.out") already"
code=$(printf '%s\n' "$key" |
  curl -q -sS --retry 4 --retry-all-errors --retry-max-time 60 --max-time 60 -o /dev/null -w '%{http_code}' \
    --aws-sigv4 aws:amz:auto:s3 -H 'Content-Type: application/vnd.reservoir.outputs+json-lines' \
    -H 'If-None-Match: *' -K - -T "$dir/outputs.jsonl" "$mappings") || fail "could not upload the mappings"
case $code in
  200) echo "mappings uploaded to $mappings" ;;
  412) echo "the bucket has mappings at $mappings already; they stay as they are" ;;
  *) fail "the bucket answered $code to the upload of the mappings" ;;
esac
