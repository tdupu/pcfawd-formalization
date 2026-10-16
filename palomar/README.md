# Palomar submission project

This directory is the Lake project selected for the [Palomar registry](https://palomar-registry.org/)
submission. The proof development is the contained path dependency `../lean`.

| File | Role |
| --- | --- |
| `PcfChallenge.lean` | The statement: Mathlib imports only. It defines the notions used in the statement and states the three compared theorems with `sorry`. Its definitions are byte-identical to `../lean/Pcf/Palomar/Statement.lean`. |
| `PcfSolution.lean` | The proof: imports the development, which proves the three theorems. `../lean/Pcf/Palomar/Bridge.lean` shows the statement is equivalent to the development's `Pcf.pcfAllTheWayDown_charZero`. |
| `comparator.json` | Compared theorems: `Pcf.Palomar.pcfAllTheWayDown_charZero`, `Pcf.Palomar.existsUnique_isNormalizationLift`, `Pcf.Palomar.exists_pointClosure_restriction`. Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`. |
| `formalization.yaml` | Palomar metadata: authors, licence, classification, sources, automation, review. |

Submission parameters: project path `palomar`, Comparator configuration
`palomar/comparator.json`, metadata `palomar/formalization.yaml`.

The theorem is conditional on two hypotheses, an affine form of Zariski–Nagata purity
(Stacks 0BMB) and an affine form of Abhyankar's lemma (Stacks 0EYG/0EYH) for algebras in which
every positive integer is invertible. What the statement does and does not claim is in
`formalization.yaml` and Entry 0 of `../lean/PALOMAR.md`.

Build with `lake build` in this directory.
