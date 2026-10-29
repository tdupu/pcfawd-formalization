# `paper-p.tex` formalization target

This dedicated Lake project exports two source-facing instances of Theorem A
from `paper-p.tex`: positive characteristic with
prime-to-`p` monodromy, and characteristic zero without a monodromy premise.
The shared `../../library/Pcf/` library provides the actual recursive
all-subvariety result. Run `lake build main` here.

These entry points cover the headline theorem in its two characteristic cases.
They do not certify every supporting statement or example in `paper-p.tex`;
that manuscript needs its own full claim-by-claim fidelity review. Its formal
PCF premise is `Pcf.IsWeightedNormalizedPCFDownstairs`, and its recursive
conclusion is `Pcf.IsPCFAllSubvarieties` on actual proper reduced integral
subvariety returns. `main.lean` prints both elaborated types and transitive
axioms.
