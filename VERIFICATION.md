# Checking the formalization

The Comparator configuration selects nineteen results. The companion manuscript has 36 pages. The proof sources, Solution, dependency pins and theorem selection are unchanged from the complete-paper source supplied for this release.

The independent Challenge states the selected results and their definitions in 995 lines and 91,105 bytes. Unreferenced numerical certificate data remains in the Solution library. Twenty-seven elementary `Nat.AtLeastTwo` facts reproduce the numeral auxiliaries used by Lean when elaborating the original definitions; each uses the same standard arithmetic instance proof as the Solution. They preserve the correspondence of elaborated declarations without importing project proofs into the Challenge.

The manual workflow `.github/workflows/palomar-p079.yml` runs Palomar's full mechanical check. Its reports identify the exact repository commit, Challenge, theorem selection, toolchain and kernel results. Consult the report for the commit being examined: a successful source build alone is not a Comparator or all-kernel pass.

[Cloud verification runs](https://github.com/mmislan/palomar-p079-distributive-phosphorylation/actions/workflows/palomar-p079.yml)
