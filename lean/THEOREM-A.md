# Theorem A: characteristic zero, characteristic p, all codimensions

Source: `latex/paper-p.tex` in the `pcf` working repository, Theorem
`thm:A`, Definition `def:pcfawd-allsubvar`, and the normalized blow-up
argument `thm:allcodim-normal`. Imported from `pcf` branch
`codex/pcfawd-charp-allcodim` at commit `f443dac`.

## Statements

- `Pcf.isPCFAllSubvarieties_charZero_of_downstairsPCF` proves the
  characteristic-zero case.
- `Pcf.isPCFAllSubvarieties_charP_of_downstairsPCF` proves the
  positive-characteristic case with prime-to-`p` monodromy.
- `Pcf.IsPCFAllSubvarieties` quantifies over every recursion depth, every
  proper integral closed subvariety, every preperiod, and every positive
  period. Its return morphisms act on the original reduced point closures.

`IsWeightedNormalizedPCFDownstairs` counts the images on the original
scheme of weighted postcritical divisors on the actual normalization lift.
`isWeightedNormalizedPCFDownstairs_iff` proves that this set is finite
exactly when the lifted weighted postcritical set is finite; the reverse
implication uses finite fibres of the normalization morphism.

The proof derives generic fibre multiplicity one in characteristic zero
and a prime-power multiplicity in characteristic `p`, bounds the bad
codimension-one points of the centre, and applies a tame chart to the
finite map of normalized Rees blow-ups. The valuation comparison makes
the normalized return étale outside a fixed finite set. The finite-cover
induction and PCF transfer then give the recursive statement.

## Verification

On the source feature branch, `lake build` completed 4,058 jobs after
the final theorem. `#print axioms` on both source-facing theorems and the
downstairs equivalence returned only `propext`, `Classical.choice`, and
`Quot.sound`. The comparator's three intentional `sorry` declarations
in `PcfChallenge.lean` are not dependencies of these theorems.

The destination branch's final full `lake build` completed 4,058 jobs at
`/private/tmp/pcfawd-transfer-final-build.log`. Its three printed axiom
sets are again exactly `propext`, `Classical.choice`, and `Quot.sound`.
All 461 transferred `lean/Pcf/` files were compared byte for byte with
the checked source branch. The destination's incomplete ignored Lake
package cache was preserved as `.lake/packages.incomplete`; the build used
the complete local package cache from `pcf` through an ignored symlink.
