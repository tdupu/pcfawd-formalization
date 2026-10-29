# Axiom and trust scope

The target imports the parent `Pcf` library and proves its two paper-facing
Theorem A entry points by applying the existing characteristic-specific
theorems. `#print axioms` in `main.lean` checks their transitive dependencies.
The current builds report only `propext`, `Classical.choice`, and `Quot.sound`
for both declarations. This does not certify every supporting claim or example
in `paper-p.tex`.
