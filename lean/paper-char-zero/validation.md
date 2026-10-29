# Validation of `paper-char-zero`

Source manuscript: `paper.tex` (private, not in this repository), SHA-256
`9b2fee2d7c2a63f30c895d3e044406c3aa8b7594ea42addc7062aa6bb8bc4c3d`.
`main.lean` SHA-256
`e3c47dee0a7e590f41c3d222ec73c3b3ab10011aff8b8c3b2e817baaf34ff25e`.
Lean 4.35.0; Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

On 2026-10-28, `lake build main PaperCharZeroChallenge PaperCharZeroSolution`
succeeded from this directory with 4469 jobs and no errors. The same command
succeeded in the authors' private development checkout, whose copies of this
project's Lean files, the 64 `Pcf/PaperCharZero` modules and the 31
`CharZeroPaper*` example modules are byte-identical to these. `lake build` of
the parent `lean/` library also succeeded here (4059 jobs).

Every one of the 2093 `#print axioms` results in the package build is a subset
of `propext`, `Classical.choice`, `Quot.sound`. In particular
`PaperCharZero.theoremA`, `PaperCharZero.cor_pcfawd`, and the four selected
`PaperCharZero.Palomar` Solution declarations print exactly these three. The
only `sorry` warnings are the four intentional theorem placeholders in
`PaperCharZeroChallenge.lean`, which the Solution does not import.

`readme.md` maps each manuscript label to its declarations and records the
modeling choices. The complex-analytic local-degree sentence of
`rem:why-normalized` is not formalized.

The target-specific Palomar package is documented in `palomar-package.md`.
Local build, export comparison, and kernel replay are not a substitute for
Palomar's exact-commit preflight.
