#!/usr/bin/env bash
# Uploads a staged build to the bucket of Lake's cache. Only the workflow
# cache-upload runs this, from main's copy, with the bucket's key.
#
#   cache-upload.sh DIR ARTIFACTS MAPPINGS
#
# DIR is what a run of CI staged with `lake cache stage`: the build archives,
# each named `<hash>.ltar`, and `outputs.jsonl`, the mappings. ARTIFACTS is
# the address under which the archives go, as `<hash>.art`. MAPPINGS is the
# whole address of the mappings file. The key comes on standard input, as the
# line `user = "<access key>:<secret>"` of a curl config, so that it is in no
# argument list.
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
# - An archive that the bucket has is not uploaded again, so nothing in the
#   bucket is replaced.
# - The mappings go last, so that a commit's mappings never name an archive
#   that is not there.
#
# If anything is wrong the script says what and exits with 1, and nothing or
# only archives have been uploaded: archives without mappings do no harm.
set -euo pipefail

dir=${1:?the staged directory} artifacts=${2:?the address of the archives} mappings=${3:?the address of the mappings}
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

# Which of the named archives the bucket has: requests without a key.
while read -r hash; do
  printf 'url = "%s/%s.art"\noutput = "/dev/null"\n' "$artifacts" "$hash"
done < "$work/named" > "$work/head.cfg"
if [ -s "$work/head.cfg" ]; then
  curl -q -sS -Z --parallel-max 32 --retry 5 --retry-all-errors --max-time 600 -I \
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
      printf 'upload-file = "%s"\nurl = "%s"\n' "$dir/$hash.ltar" "$url" >> "$work/put.cfg" ;;
    *) fail "the bucket answered $code for an archive" ;;
  esac
done < "$work/head.out"
echo "archives named: $(wc -l < "$work/named"), in the bucket: $have, to upload: $send"

# Hetzner answers 503 to many uploads at once; curl tries those again.
if [ "$send" -gt 0 ]; then
  { printf '%s\n' "$key"; cat "$work/put.cfg"; } |
    curl -q -sS -Z --parallel-max 16 --retry 8 --retry-all-errors --max-time 900 --fail -o /dev/null \
      --aws-sigv4 aws:amz:auto:s3 -H 'Content-Type: application/vnd.reservoir.artifact' -K - ||
    fail "could not upload the archives"
fi
printf '%s\n' "$key" |
  curl -q -sS --retry 8 --retry-all-errors --max-time 300 --fail -o /dev/null \
    --aws-sigv4 aws:amz:auto:s3 -H 'Content-Type: application/x-ndjson' -K - -T "$dir/outputs.jsonl" "$mappings" ||
  fail "could not upload the mappings"
echo "mappings uploaded to $mappings"
