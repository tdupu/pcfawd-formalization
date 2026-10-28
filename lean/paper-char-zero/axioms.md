# Axiom census

The `#print axioms` checks in `main.lean` report the following for both
`PaperCharZero.theoremA` and `PaperCharZero.cor_pcfawd`:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical axioms. Neither theorem depends on
`sorryAx` or a project-specific mathematical axiom. The geometric inputs
Zariski--Nagata purity and Abhyankar's lemma are supplied by proved
declarations in the parent `pcfawd` library. The explicit hypotheses in
the theorem types are the geometric setting, characteristic zero,
preperiodicity, and PCF, as stated in the paper.
