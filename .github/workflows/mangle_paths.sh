#!/usr/bin/env bash
lean_version="$(sed '/^lean_version/!d;s/.*"\(.*\)".*/\1/' doc-gen/leanpkg.toml)"
mathlib_git_hash="$(sed '/rev/!d;s/.*"\([a-z0-9]*\)".*/\1/' dic-gen/leanpkg.toml)"
cd doc-gen
sed -i "s/rev = \"\S*\"/rev = \"$mathlib_git_hash\"/" leanpkg.toml

# Force doc_gen project to match the Lean version used in CI.
# If they are incompatible, something in doc_gen will fail to compile,
# but this is better than trying to recompile all of mathlib.
elan override set "$lean_version"

leanproject get-mathlib-cache
echo -e "path ../src" >> leanpkg.path
cat leanpkg.path

(cd doc-gen/src;
 find "." -name \*.lean -not -name all.lean \
     | sed 's,^\./,,;s,\.lean$,,;s,/,.,g;s,^,import ,' \
     | sort >./all.lean)

cat ../src/all.lean
lean --path
