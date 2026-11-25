#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$src/../../.." && pwd)
cd "$project/lean"
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.CoverCircuitList PEqualNP.MetaComplexity.Helpers.LineDegTest PEqualNP.MetaComplexity.Helpers.LocalPrivate2 PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.Support PEqualNP.Outside.L_meta_4342 PEqualNP.Outside.L_meta_5670
out=$(mktemp -d)
trap 'rm -rf -- "$out"' EXIT
export LEAN_PATH="$out:$(lake env printenv LEAN_PATH)"
cd "$src"
for mod in Extract Boundary Compression Factor BoundaryCount BothShores OptionalProjection ConeBudget Application Closed WireFacts PureTriples Pure SevenRigidity ExactNeighborhood FanoFloor Saturated Thirteen Numeric AtMostOne ThirteenReal Desk OrBudget FanoBudget Arbitrary FourteenReal Tree; do
  lean -j1 -DwarningAsError=true -o "$out/$mod.olean" "$mod.lean"
done
