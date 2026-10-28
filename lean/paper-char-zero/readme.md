# Characteristic-zero proof for `latex/paper.tex`

This is a dedicated Lake project for the current characteristic-zero paper.
It pins Lean 4.35.0 and uses the existing `pcfawd` library in the parent
`lean/` directory as a local dependency. No existing Lean source is changed.
The folder contains the paper-facing proof and its build configuration; the
geometric lemmas remain in the parent library, so it is not an independent
reimplementation of purity or Abhyankar's lemma.

From this directory, run `lake build main`. The target is explicit in
`defaultTargets`; `lake build` checks it too. The last two commands in
`main.lean` print the transitive axioms of both headline theorems.

## Source map

| Paper claim | Lean declaration | Meaning |
| --- | --- | --- |
| `def:crit-branch`, `def:pcf` | `Pcf.IsNormalizedPCFOfFiniteType` | Finiteness of the forward orbit of the normalized branch locus of the actual normalization lift. |
| `thm:purity`, `thm:abhyankar` | `Pcf.pcfAllTheWayDownLocalTheorems_proved` | The two proved local inputs; no hypothesis is added to the headline theorem. |
| `thm:bounding` and `thm:normal-invariant` | `Pcf.periodicDivisor_isNormalizedPCFOfFiniteType` and its dependencies | The existing geometric development proves the periodic-divisor return theorem through the bounding argument. |
| `thm:A` = `thm:general` | `PaperCharZero.theoremA` | The actual reduced image divisor of `A` under `f^r` has a normalized-PCF return under `f^p`, with `p ≥ 1`. |
| `cor:pcfawd` | `PaperCharZero.cor_pcfawd` | Induction on the number of successive divisor returns. |

The paper assumes varieties are integral, separated, and of finite type over
a characteristic-zero field. The Lean theorem uses an integral scheme with a
locally finite type structure map and Noetherian hypotheses, and omits
separatedness because it is unused. For a variety, these additional
Noetherian hypotheses hold. `SchemeDivisorPoint X` is a codimension-one point,
whose reduced closure is the paper's integral effective divisor. The output
is the induced map on the actual reduced closure of `f^r(A)`. The full type
and axiom printouts are emitted by the build of `main.lean`.

This folder covers the two headline assertions. It does not separately
restate the examples or every supporting lemma in `paper.tex`.
