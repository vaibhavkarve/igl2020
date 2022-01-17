##!/usr/bin/env bash
cd doc-gen
lean -v
# the json and diagnostics are emitted on stdout, but the json is always the last (very long) line.
lean src/entrypoint.lean > export.json || true
head -n -1 export.json
tail -n1 export.json > export2.json
rm export.json
mv export2.json export.json
head -c1000 export.json
