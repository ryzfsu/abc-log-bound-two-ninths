#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."

expected_statement=54b649bd8da66280550b93f3fb758c3a72c9454e333fe20217c82966514dd8ca
printf '%s  AbcTwoNinths/Statement.lean\n' "$expected_statement" | sha256sum --check --status

if [[ -e .lake/build || -L .lake/build ]]; then
  printf '%s\n' 'Use a fresh checkout with no project .lake/build directory.' >&2
  exit 1
fi
if [[ -e .git ]]; then
  git diff --quiet HEAD --
fi

unset LEAN_PATH LEAN_SRC_PATH
export LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR=
source_hashes() {
  find . \( -name .lake -o -name .git \) -prune -o -type f \( \
    -name '*.lean' -o -name lean-toolchain -o -name lake-manifest.json -o \
    -name comparator.json -o -name formalization.yaml -o -name LICENSE -o -name NOTICE -o \
    -path ./verification/verify.sh \) -print0 | LC_ALL=C sort -z | xargs -0 sha256sum
}
source_hashes > verification/source-sha256.txt

lake -R -Kstrict=true --no-cache build +Solution:olean +PaperMap:olean 2>&1 | tee verification/build.txt
test ! -e .lake/build/lib/lean/Challenge.olean
lake -R -Kstrict=true env lean -DwarningAsError=true SolutionAxioms.lean | tee verification/axioms.txt
expected_axioms="'AbcTwoNinths.twoNinths' depends on axioms: [propext, Classical.choice, Quot.sound]"
if [[ $(< verification/axioms.txt) != "$expected_axioms" ]]; then
  printf '%s\n' 'Unexpected axiom report.' >&2
  exit 1
fi

lake -R --no-cache build +Challenge:olean 2>&1 | tee verification/challenge.txt
lake -R env lean -DwarningAsError=true --run verification/StatementIdentity.lean > verification/statement-identity.json
lake -R -Kstrict=true --no-cache build +Solution:olean +PaperMap:olean 2>&1 | tee verification/build-after-challenge.txt
source_hashes | cmp verification/source-sha256.txt -
