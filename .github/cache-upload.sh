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
# The bucket is asked only about the archives that KNOWN does not name: a
# mappings file is uploaded after its archives, and nothing in the bucket is
# deleted, so the archives it names are there. Without KNOWN the bucket is
# asked about every archive, some 1,500 requests, and several such uploads
# at once were more than Hetzner answers: it sent 503, curl tried again, and
# uploads stood for 20 minutes on runners that builds were waiting for. If
# the bucket should ever lose an archive that KNOWN names, a commit's
# mappings name an archive that is not there, and a build compiles that
# module. If objects are ever made to expire, this must be thought through
# again.
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
# - Nothing in the bucket is replaced. An archive that the bucket has is not
#   sent, and every upload carries `If-None-Match: *`, which makes the bucket
#   refuse it (412) if the name is taken, also when two uploads race. A
#   commit's mappings that are there already stay as they are.
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
    (.[1] | type == "string" and test("^[0-9a-f]{16}\\.ltar$")))' "$dir/outputs.jsonl" >/dev/null ||
  fail "the mappings file is not of the form that Lake writes for packed archives"
jq -r -s '.[1:][] | .[1] | sub("\\.ltar$"; "")' "$dir/outputs.jsonl" | sort -u > "$work/named"

# The archives that KNOWN names are in the bucket. A KNOWN that is not of
# the form of a mappings file counts for nothing.
: > "$work/known"
if [ -n "$known" ] && [ -f "$known" ]; then
  jq -r -s 'if (.[0] | type == "string") and all(.[1:][]; type == "array" and length == 2 and (.[1] | type == "string" and test("^[0-9a-f]{16}\\.ltar$")))
    then .[1:][] | .[1] | sub("\\.ltar$"; "") else empty end' "$known" 2>/dev/null | sort -u > "$work/known" || : > "$work/known"
fi
comm -23 "$work/named" "$work/known" > "$work/ask"
# Which of the others the bucket has: requests without a key.
while read -r hash; do
  printf 'url = "%s/%s.art"\noutput = "/dev/null"\n' "$artifacts" "$hash"
done < "$work/ask" > "$work/head.cfg"
if [ -s "$work/head.cfg" ]; then
  curl -q -sS -Z --parallel-max 32 --retry 3 --retry-all-errors --retry-max-time 60 --max-time 30 -I \
    -w '%{http_code} %{url_effective}\n' -K "$work/head.cfg" > "$work/head.out" || fail "could not ask the bucket which archives it has"
fi
: >> "$work/head.out"
have=0 send=0
: > "$work/put.cfg"
while read -r code url; do
  hash=${url##*/}; hash=${hash%.art}
  case $code in
    200) have=$((have + 1)) ;;
    404)
      [ -f "$dir/$hash.ltar" ] || fail "the mappings name the archive $hash, which is neither staged nor in the bucket"
      send=$((send + 1))
      printf 'upload-file = "%s"\nurl = "%s"\noutput = "/dev/null"\n' "$dir/$hash.ltar" "$url" >> "$work/put.cfg" ;;
    *) fail "the bucket answered $code for an archive" ;;
  esac
done < "$work/head.out"
echo "archives named: $(wc -l < "$work/named"), known to be in the bucket: $(comm -12 "$work/named" "$work/known" | wc -l), asked about: $(wc -l < "$work/ask"), of which there: $have, to upload: $send"

# Hetzner answers 503 to many uploads at once; curl tries those again, and a
# broken connection too. An answer such as 403 or 412 is no error to curl
# without `--fail`, so it is not tried again. 412 means that the name was
# taken meanwhile, also by this upload's own first try, which is as good as
# uploaded. Each upload's answer goes to /dev/null by a line of its own in
# the config: one `-o` on the command line serves only the first, and the
# text of a 412 among the status codes failed uploads that had lost a race
# for an archive, as two runs of one batch of the merge queue do. The tries are few and bounded in time: a run's work that does
# not reach the bucket costs a later build some compiling, and an upload
# that hangs costs a runner that a build is waiting for. Two of the first
# uploads hung for the job's whole 20 minutes.
if [ "$send" -gt 0 ]; then
  { printf '%s\n' "$key"; cat "$work/put.cfg"; } |
    curl -q -sS -Z --parallel-max 16 --retry 4 --retry-all-errors --retry-max-time 90 --max-time 120 -w '%{http_code}\n' \
      --aws-sigv4 aws:amz:auto:s3 -H 'Content-Type: application/vnd.reservoir.artifact' \
      -H 'If-None-Match: *' -K - > "$work/put.out" || fail "could not upload the archives"
  if grep -qvE '^(200|412)$' "$work/put.out"; then
    fail "the bucket answered $(grep -vE '^(200|412)$' "$work/put.out" | sort | uniq -c | tr '\n' ' ') to uploads of archives"
  fi
fi
code=$(printf '%s\n' "$key" |
  curl -q -sS --retry 4 --retry-all-errors --retry-max-time 60 --max-time 60 -o /dev/null -w '%{http_code}' \
    --aws-sigv4 aws:amz:auto:s3 -H 'Content-Type: application/vnd.reservoir.outputs+json-lines' \
    -H 'If-None-Match: *' -K - -T "$dir/outputs.jsonl" "$mappings") || fail "could not upload the mappings"
case $code in
  200) echo "mappings uploaded to $mappings" ;;
  412) echo "the bucket has mappings at $mappings already; they stay as they are" ;;
  *) fail "the bucket answered $code to the upload of the mappings" ;;
esac
