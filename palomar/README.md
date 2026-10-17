# Palomar submission project

This directory is the Lake project selected for the [Palomar registry](https://palomar-registry.org/)
submission. The proof development is the contained path dependency `../lean`.

| File | Role |
| --- | --- |
| `PcfChallenge.lean` | The statement: Mathlib imports only. It defines the notions used in the statement and states the three compared theorems with `sorry`. Its definitions are identical to `../lean/Pcf/Palomar/Statement.lean` (only the module docstring differs). |
| `PcfSolution.lean` | The proof: imports `Pcf.Palomar.Unconditional`, which proves the main theorem from the development's `Pcf.pcfAllTheWayDown_charZero` with Zariski–Nagata purity and Abhyankar's lemma supplied as proved theorems. `../lean/Pcf/Palomar/Bridge.lean` shows the statement's notions are equivalent to the development's. |
| `comparator.json` | Compared theorems: `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional`, `Pcf.Palomar.existsUnique_isNormalizationLift`, `Pcf.Palomar.exists_pointClosure_restriction`. Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`. |
| `formalization.yaml` | Palomar metadata: authors, licence, classification, sources, automation, review. |

Submission parameters: project path `palomar`, Comparator configuration
`palomar/comparator.json`, metadata `palomar/formalization.yaml`.

The main theorem has no hypotheses beyond those in its statement. Affine forms of
Zariski–Nagata purity (Stacks 0BMB) and of Abhyankar's lemma (Stacks 0EYG/0EYH, for algebras in
which every positive integer is invertible) are proved in `../lean` and used in the proof; they
are not hypotheses. What the statement does and does not claim is in `formalization.yaml` and
Entry 0 of `../lean/PALOMAR.md`.

Build with `lake build` in this directory.
