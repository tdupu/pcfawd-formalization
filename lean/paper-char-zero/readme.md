# Characteristic-zero divisorial paper formalization

This Lake project formalizes the characteristic-zero manuscript
*PCF all the way down* (`paper.tex`, cited by its LaTeX `\label`s). The
manuscript is private and not included in this repository. The parent `../Pcf/`
library supplies the geometric proofs and is a local Lake dependency. From this
directory, run `lake build main PaperCharZeroChallenge PaperCharZeroSolution`.

## Checked source map

Theorem names below are prefixed `Pcf.PaperCharZero.` (support) or
`Pcf.Examples.` (examples) unless shown in full.

| `paper.tex` claim | Lean entry | Scope and modeling notes |
| --- | --- | --- |
| `thm:A`, `thm:general` | `PaperCharZero.theoremA` | Normalized PCF of the actual reduced image of every preperiodic integral effective divisor under its specified return. |
| `cor:pcfawd`, `def:pcfawd` | `PaperCharZero.cor_pcfawd`, `pcfAllTheWayDown_iff_at_dimension_bound`, `dimension_zero_isPCFAllTheWayDown` | PCF on every successive divisor return; the depth predicate stabilizes at the dimension bound and is automatic in dimension zero. |
| `thm:bounding` | `bounding_theorem` | The literal exceptional set Σ is proper and closed, and g is étale at every divisor of A whose image is not contained in Σ. |
| `thm:abhyankar` | `abhyankar_lemma` | The manuscript's explicit étale-local form: one nonzerodivisor `a`, `D ×_U Spec R = V(a)`, components `R[z]/(z^{e_i} − u_i a)`. |
| `thm:purity` | `zariski_nagata_purity` | Local scheme form with the manuscript's hypotheses. |
| `lem:lift` | `Pcf.finiteDominantFiniteType_divisor_lift` | Generic-point form. |
| `lem:dictionary` | `ramificationIdx_eq_one_iff_etale_at_divisor_charZero` | Source normality is not needed. |
| `lem:etale-normalized-index` | `etale_normalized_index` | Every normalization branch above the divisor. |
| `lem:restriction` | `integral_effective_divisor_restriction` | Reduced image, codimension one, integral, finite surjective restriction. |
| `lem:tower` | `normalized_branch_tower` | Exact equality for composable finite dominant maps. |
| `lem:normalization` | `normalization_postcritical_and_pcf` | Both assertions. |
| `lem:covers` | `Pcf.isNormalizedPCFOfFiniteType_of_cover` | Finite-type scheme form. |
| `lem:finitely-many` | `finite_integral_effective_divisors_in_closed` | Divisor and subscheme forms. |
| `prop:pcf-equiv` | `scheme_isNormalizedPCF_iff_branch_preperiodic`, `scheme_isNormalizedPCF_iff_critical_support_preperiodic` | All three conditions. |
| `prop:iterates` | `normalized_iterates` | All four assertions. |
| `eq:standard-piece` | `standard_piece` | Quotient-by-parameter and reduction chain. |
| `ex:squaring-PN` | `CharZeroPaperSquaringBranch`, `CharZeroPaperSquaringIndex`, `CharZeroPaperSquaringRestriction.hyperplane_restriction_squaring_isPCF`, `CharZeroPaperProjectiveAllTheWayDown` | Every N ≥ 1: exact branch locus, index 2 along each coordinate hyperplane, restriction identified with squaring on ℙ^{N−1}, PCF, PCF all the way down, and the diagonal is never a branch component of an iterate. |
| `ex:koch`, `ex:dupont` | `CharZeroPaperPlaneBranch`, `CharZeroPaperPlaneProjective`, `CharZeroPaperProjectiveAllTheWayDown` | Finite surjective maps of ℙ², exact critical, branch and postcritical sets, PCF. |
| `ex:pinched` | `CharZeroPaperPinched.*` | All clauses. The nonreduced-fibre and non-étale branch loci and their postcritical sets are defined in `CharZeroPaperPinchedNode` for this example. |
| `ex:cusp` | `CharZeroPaperCuspCanonical` | Canonical normalization, empty normalized branch, branch intersection at the origin, strict inclusion, singular origin. |
| `ex:smooth-restriction` | `CharZeroPaperSmoothRestriction`, `CharZeroPaperSmoothBranch` | All clauses. |
| `ex:branch-singular` | `CharZeroPaperConeBranch.ex_branch_singular` | All clauses. The quotient by ±1 is the ring of invariants. |
| `ex:branch-sing-B` | `CharZeroPaperSingularImageGeometry.sing_term_necessary`, `CharZeroPaperSingularImageBounding.singB_term_cannot_be_dropped` | All clauses, including that the Sing(B) term of Σ in `bounding_theorem` cannot be dropped. Uses an algebraically closed field. |
| Introduction, classical PCF on ℙ¹ | `projLine_isNormalizedPCF_iff_jacobian`, `projLine_ratPoint_critical_iff_derivative` | For maps given by basepoint-free binary forms. |
| `rem:why-normalized` | `CharZeroPaperCuspHomeomorph` | The cusp normalization is an unbranched homeomorphism. The complex-analytic local-degree sentence is not formalized. |

`main.lean` prints the elaborated headline types and their transitive axioms.
Each support and example module ends with `#print axioms` for its declarations.
See `validation.md` for the tested snapshot and `axioms.md` for trust scope.

The Palomar Challenge, Solution, Comparator configuration, and metadata for
this target are described in `palomar-package.md`. The Palomar entry selects the
four headline declarations listed there; the other results above are built by
this project but are not selected results.
