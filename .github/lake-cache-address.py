#!/usr/bin/env python3
"""Where a Lake cache service of `.github/lake-config.toml` keeps things.

    lake-cache-address.py SERVICE TOOLCHAIN

Prints two lines: the address of the service's archives, to which Lake adds
`/<hash>.art`, and the address of its mappings for builds with TOOLCHAIN (the
content of `lean-toolchain`) on GitHub's runners, to which Lake adds
`/<commit>.jsonl`.

The second is what Lake's `s3RevisionUrl` (Lake/Config/Cache.lean) forms for
a service without package scopes: the service's `revisionEndpoint`, then
`pt/<platform>`, then `tc/<toolchain>` with `/` as `--` and `:` as `---`.
The workflow cache-upload writes to these addresses, and reads main's
mappings at them, and ci.yml asks the bucket at them. Both get them here, so
that they cannot drift apart. If
Lake changes the form, uploads land where Lake does not look: builds then
find nothing in the bucket, and nothing fails.
"""
import re
import sys
import tomllib

PLATFORM = "x86_64-unknown-linux-gnu"

service, toolchain = sys.argv[1], sys.argv[2].strip()
if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?", toolchain):
    sys.exit("%r does not name a release of Lean" % toolchain)
with open(__file__.rsplit("/", 1)[0] + "/lake-config.toml", "rb") as f:
    services = {s["name"]: s for s in tomllib.load(f)["cache"]["service"]}
if service not in services:
    sys.exit("lake-config.toml has no cache service %r" % service)
s = services[service]
if s.get("hasPackageScopes", True):
    sys.exit("the cache service %r has package scopes, which this script does not form" % service)
print(s["artifactEndpoint"])
print("%s/pt/%s/tc/%s" % (s["revisionEndpoint"], PLATFORM, toolchain.replace("/", "--").replace(":", "---")))
