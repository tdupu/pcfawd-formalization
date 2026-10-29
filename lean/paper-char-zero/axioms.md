# Axiom and trust scope

The active headline declarations are `PaperCharZero.theoremA` and
`PaperCharZero.cor_pcfawd`. The project builds proved local purity and
Abhyankar inputs through the parent library; their desired conclusion is not
an input hypothesis. `#print axioms` in `main.lean` is the machine check for
the transitive axiom sets. The latest successful build is recorded in
`validation.md`.

The supporting and example modules have their own `#print axioms` probes.
Every printed axiom set in the full package build is a subset of Lean's
logical axioms `propext`, `Classical.choice`, and `Quot.sound`. This is a
claim about the printed declarations. Assumptions carried as hypotheses or
as definitions chosen to model a manuscript notion are not visible to
`#print axioms`; `readme.md` lists the modeling choices.
