# Validation of `char-p/lean`

Source manuscript: `paper-p.tex` (characteristic-`p` version; not in this
repository). Formal target: `main.lean` in this directory, depending on the
shared `../../library` (Lake package `pcfawd`, library `Pcf`).

On 2026-10-29, after the repository was reorganized into `library/`,
`char-zero/` and `char-p/`, `lake build` succeeded here (3982 jobs) and in
`../../library` (4439 jobs). `PaperCharP.theoremA_positiveCharacteristic`,
`PaperCharP.theoremA_characteristicZero` and
`Pcf.isPCFAllSubvarieties_charP_of_downstairsPCF` print exactly the axioms
`propext`, `Classical.choice`, `Quot.sound`; every printed axiom set in the
build is a subset of these. This file does not claim a fidelity audit of
`paper-p.tex`; see [`../THEOREM-A.md`](../THEOREM-A.md).
