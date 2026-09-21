# AXIOMS.md — assumed inputs of the Lean formalization

| Field | Value |
| --- | --- |
| Repo | `pcf` |
| Scope | `lean/` |
| Status | Draft |
| Date | `2026-09-20` |
| Manuscript | `latex/pcf.tex` |
| Toolchain | Lean `4.34.0`, Mathlib `v4.34.0` (`5ed296525643`) |

This is the *axiom census* of the formalization, in the sense used by the
`gq2` project: the formalization is deliberately **conditional**, and this file
names every input it assumes instead of proving.

## How to read `#print axioms` here

`#print axioms` on every theorem in this development reports only the standard
logical axioms `propext`, `Classical.choice`, `Quot.sound`. **That is not a
claim that nothing is assumed.** The assumed mathematics enters as *fields of
structures* (`Pcf.DivDyn`, `Pcf.PcfSetup`), i.e. as hypotheses, not as Lean
`axiom` declarations — so it is invisible to `#print axioms` by construction.
A theorem of the form `theorem t (h : P) : Q` has no axioms and still proves
only `P → Q`.

There is no `sorry`, no `axiom`, no `admit` and no `native_decide` anywhere in
`lean/Pcf/`. The conditionality is entirely in the list below.

## A. Modelling assumptions (the abstraction itself)

The manuscript is scheme-theoretic. Mathlib has no theory of normal varieties,
normalization, branch divisors, Zariski–Nagata purity or Abhyankar's lemma, so
the development does **not** construct a `DivDyn` from a morphism of schemes.
It axiomatizes the divisorial bookkeeping instead.

| ID | Assumption | Manuscript source |
| --- | --- | --- |
| A1 | The primes of the normalized model of a variety form a type `P`, and a finite dominant self-map induces a *function* `step : P → P` (image of a prime is a prime). | §1 Conventions |
| A2 | Ramification indices are captured by a function `ram : P → ℕ` with `ram P' = e(P'/g(P'))`, positive everywhere. | Definition 2.2 |
| A3 | Branching is modelled by `1 < ram`, i.e. by `e > 1` alone. Definition 2.2's second clause (inseparable residue extension) is **not** modelled. | Definition 2.2, Definition 2.3 and Remark 7.2 |
| A4 | The ramification index of the `m`-th iterate equals `∏_{i<m} ram (stepⁱ ·)`. In Lean this is the *definition* of `DivDyn.iterRam`, so multiplicativity of ramification in towers is assumed, not derived. | §3, proof of Proposition 3.3 |
| A5 | The geometric objects `Sing(X)`, `Sing(A)` and `A ∩ E` are represented by abstract sets of primes (`PcfSetup.sing`, `PcfSetup.meets`). No scheme-theoretic content is attached to them. | Proposition 4.1 |

**Consequence.** A3 restricts the development to the characteristic-zero
setting of Theorem A, where non-étaleness at a source DVR is exactly `e > 1`.
Example 7.4 shows that the wild positive-characteristic statement is false, so
nothing is lost for Theorem A and nothing is claimed beyond it.

## B. Assumed theorems (the interfaces to the literature)

The development has **two layers**, and it matters which one a statement lives in.

* The **abstract layer** (`Pcf/Dynamics.lean`, `Pcf/Restriction.lean`) proves Theorem A
  from structure fields. It is what §C below describes.
* The **geometric layer** (`Pcf/Noetherian.lean`, `Pcf/Purity.lean`,
  `Pcf/Ramification.lean`, `Pcf/LocalModel.lean`, `Pcf/Geometry.lean`) proves
  Proposition 4.1 and the finiteness statements outright, from strictly smaller inputs.

The geometric layer **is not yet wired into** the abstract layer: nothing constructs a
`Pcf.PcfSetup` from a `Pcf.Prop41Data`. So the fields below are still hypotheses *of the
structures that Theorem A consumes*, even where the corresponding mathematical statement
is now a theorem elsewhere in the development. That gap is recorded honestly in the last
column, and closing it is the obvious next task.

### B.1 Fields of `DivDyn` and `PcfSetup` (what Theorem A still assumes)

| ID | Lean field | Statement assumed | Now proved elsewhere? |
| --- | --- | --- | --- |
| B1 | `DivDyn.step_surjective` | Lying over: every prime is the image of a prime (proof of Lemma 3.2; Stacks 00HS / 00H8). | No. |
| B2 | `DivDyn.branch_finite'` | The branch divisor has finitely many components (§2, after Definition 2.3). | **Yes** — `Pcf.PurityData.finite_isPrime_subset_nonEtale`, given only that the non-étale locus is a *proper closed subset*. |
| B3 | `PcfSetup.sing_finite` | `Sing(Y) ∩ B` and `Sing(B)` contain finitely many primes (Proposition 4.1(1)). | **Yes** — `Pcf.Prop41Data.finite_sing_subtype`. |
| B4 | `PcfSetup.meets_finite` | `B ∩ Z` contains finitely many primes (Proposition 4.1(1)). | **Yes** — `Pcf.Prop41Data.finite_meets_subtype`. |
| B5 | `PcfSetup.key` | **Proposition 4.1(2)**, applied to every iterate. | **Yes** — `Pcf.Prop41Data.notMem_branch`, from purity and Abhyankar alone. |

### B.2 What the geometric layer actually assumes

These are the irreducible inputs — the statements that are genuinely quoted from the
literature rather than derived.

| ID | Lean field | Statement assumed | Source |
| --- | --- | --- | --- |
| P1 | `PurityData.localPurity` | **Zariski–Nagata purity, local form.** If a point has codimension ≥ 1 and the morphism is étale at every codimension-one generization, it is étale there. | Stacks Tag 0BMB |
| P2 | `Prop41Data.standardForm` | **Abhyankar's lemma plus étale-local descent.** At a prime satisfying (a), (b), (c), each prime above admits an `UnramifiedWitness`: étale-locally the restriction of the cover to the divisor is an isomorphism. | Stacks Tags 0EYF, 0EYG; SGA 1 Exp. XIII Prop. 5.2 |
| P3 | `PurityData.closure_eq_univ_of_codim_eq_zero` | A point of codimension zero is a generic point. | Bookkeeping; true in an irreducible scheme |
| P4 | `PurityData.nonEtale_isClosed`, `nonEtale_ne_univ` | The étale locus is open, and the morphism is generically étale (separability). | §4, and §2's separability hypothesis |
| P5 | `Prop41Data.singSelf_isClosed`, `singSelf_ne_univ` | `Sing(B)` is a proper closed subset — a variety in characteristic zero is generically regular. | Proposition 4.1(1) |
| P6 | `Prop41Data.singAmbient_*`, `interOther_*` | The other two loci are proper closed. For `B ∩ Z` this is **proved** by `Pcf.IsPrime.inter_sUnion_ne_self`; for `Sing(Y) ∩ B` it follows from `Pcf.not_subset_of_two_le_codim` given that `Sing(Y)` has codimension ≥ 2 (normality of `Y`). | Proposition 4.1(1) |

**The global form of purity is no longer assumed.** The manuscript derives it from the
local form by hand, remarking that the SGA reference was "difficult to parse for the
present application". That derivation is now machine-checked:
`Pcf.PurityData.codim_eq_one`.

**Non-vacuity of P2.** `Pcf.LocalModel.unramifiedWitness` constructs an `UnramifiedWitness`
from an honest standard tame local model `R[z]/(z^e − ua)`, for **every** `e ≥ 1`. So P2
is satisfiable, and satisfiable with the cover genuinely ramified.

## B.3 A trap this layer closes

An independent check of this development produced the following, as a purported
counterexample to Step 3:

> Take `R = ℤ`, `a = 2`, `u = 1`, `e = 2`, so `C = ℤ[√2]` and `z = √2`. Then
> `C/(z) ≅ ℤ/2 ≅ R/(a)`, yet `2` is totally ramified in `ℤ[√2]`: `(2) = (√2)²`,
> ramification index `2`.

The computation is correct, and it refutes the claim "the two quotient *rings* are
isomorphic, therefore the ramification index is 1" — a claim the manuscript never makes.
Step 4 is about the **restriction** `g = f|_A`, whose local model is the specific map
`R/(a) → C/(z)`; the *cover* `R → C` really is ramified with index `e`, and the manuscript
says so.

The formalization now pins both halves so the confusion cannot recur:

* `Pcf.LocalModel.restrictionMap_bijective` — the named map `R/(a) → C/(z)` is bijective.
  This, not the abstract isomorphism `quotientRootEquiv`, is what Step 4 consumes.
* `Pcf.LocalModel.isNilpotent_root_mod_algebraMap` — `z` is nilpotent modulo the image of
  `a`, recording affirmatively that the cover *is* ramified along the divisor.

## C. What is proved outright (no assumption beyond A and B)

Everything in `Pcf/Dynamics.lean` and `Pcf/Restriction.lean`:

| Manuscript | Lean declaration |
| --- | --- |
| Lemma 3.2 (padding) | `Pcf.DivDyn.IsChain.extend` |
| chains ↔ iterates dictionary | `Pcf.DivDyn.exists_isChain_iff` |
| multiplicativity in towers | `Pcf.DivDyn.iterRam_add` |
| Proposition 3.3 | `Pcf.DivDyn.mem_branch_iter_iff` |
| Proposition 3.4 | `Pcf.DivDyn.mem_branch_iter_succ` |
| Proposition 3.5 | `Pcf.DivDyn.pcSet_iter`, `Pcf.DivDyn.pcf_iter_iff`, `Pcf.DivDyn.branch_iter_subset_pcSet`, `Pcf.DivDyn.step_image_pcSet_subset` |
| Definition 2.4, last clause | `Pcf.DivDyn.pcf_iff_forall_orbit_finite` |
| Remark 2.5 | `Pcf.DivDyn.pcf_of_finite_cover` |
| Theorem 5.1 = Theorem A | `Pcf.PcfSetup.res_pcf` |
| uniformity of `Σ` in `m` (the crux) | `Pcf.PcfSetup.branch_iter_subset_bound` |
| Corollary 5.2 | `Pcf.PcfSetup.res_pcf_of_iter` |
| Corollary 5.5, normalized form | `Pcf.PcfSetup.normalization_pcf` |
| Corollary 5.5, descent | `Pcf.pcf_descent` |

And, in the geometric layer, all of §4 except P1–P6:

| Manuscript | Lean declaration |
| --- | --- |
| Definition 2.1 (prime), topologically | `Pcf.IsPrime` |
| primes are incomparable | `Pcf.IsPrime.eq_of_subset_of_isPrime` |
| Proposition 4.1(1), the `Z` term | `Pcf.IsPrime.not_subset_sUnion`, `Pcf.IsPrime.inter_sUnion_ne_self` |
| Proposition 4.1(1), the `Sing(Y)` term | `Pcf.not_subset_of_two_le_codim` |
| Proposition 4.1(2), first paragraph (finiteness) | `Pcf.finite_isPrime_subset` |
| §2, finiteness of `Branch(g)` | `Pcf.PurityData.finite_isPrime_subset_nonEtale` |
| §4, purity: local form ⟹ global form | `Pcf.PurityData.codim_eq_one` |
| §4, the inner maximality step | `Pcf.PurityData.notMem_nonEtale_of_specializes` |
| Proposition 4.1, Step 3 (as a *map*) | `Pcf.LocalModel.restrictionMap_bijective` |
| the cover is ramified along the divisor | `Pcf.LocalModel.isNilpotent_root_mod_algebraMap` |
| Proposition 4.1, Step 4's final inference | `Pcf.Ramification.ramificationIdx_eq_one_of_bijective`, `Pcf.UnramifiedWitness.eq_one` |
| Proposition 4.1(2) | `Pcf.Prop41Data.notMem_branch` |
| Proposition 4.1(3) | `Pcf.Prop41Data.branch_subset_bound`, `Pcf.Prop41Data.finite_bound`, `Pcf.Prop41Data.finite_branch` |

## D. Supporting formalizations

| Manuscript | Lean file | Status |
| --- | --- | --- |
| Strategy §1 / Proposition 4.1, Step 3 (`O[z]/(z^e − ua, z) = O/(a)`) | `Pcf/LocalModel.lean` | proved |
| Example 4.4: `k[t]` is the integral closure of `k[t²,t³]` in their common fraction field, and `t ∉ k[t²,t³]` | `Pcf/Examples/Cusp.lean` (`isIntegralClosure_cuspAlg`, `isFractionRing_cuspAlg`, `X_not_mem_cuspAlg`) | proved |
| Example 4.4: the parametrization `k[x,y]/(y²−x³) → k[t]` and the Jacobian `2u` | `Pcf/Examples/Cusp.lean` (`cuspParam`, `jacobian_cuspSource`) | proved |
| Example 4.4: `B ∩ Z = {(0,0)}` | `Pcf/Examples/Cusp.lean` (`cusp_inter_branch`) | proved |
| Example 4.5: the quadric cone parametrization and the restriction `g(u) = u²` | `Pcf/Examples/Cusp.lean` (`coneParam`, `coneMap_restrict`) | proved |
| Example 6.1 (squaring map on `P¹`), Example 6.2 (diagonal squaring) | `Pcf/Examples/Squaring.lean` | proved |
| Example 7.4 (wild counterexample, `deg_c(a_n) = (p+1)^{n−1}`) | `Pcf/Examples/CharP.lean` | proved |

## E. Not formalized at all

* Definition 2.1 (prime of a variety) and the definition of `Crit`/`Branch` as
  divisors on schemes.
* The **scheme-theoretic** halves of Steps 1 and 2 of the proof of Proposition 4.1:
  choosing the affine open `U`, verifying purity's hypotheses pointwise, and the
  étale-local descent that puts the cover in standard tame form. These are P1 and P2.
  The *reasoning* that joins them to the conclusion is now proved (§C).
* The regularity remark inside the proof of Proposition 4.1, and the
  strict-henselization / étale-base-change invariance of ramification indices. In the
  Lean development that invariance is folded into P2, which delivers the witness
  directly rather than delivering a pre-base-change extension.
* The identification of `Ideal.ramificationIdx` with the manuscript's `e(𝔮/𝔪)` from
  Definition 2.2 for extensions of discrete valuation rings. Mathlib relates its two
  ramification-index definitions only under Dedekind hypotheses.
* The wiring of the geometric layer into `Pcf.PcfSetup`: nothing yet builds a
  `PcfSetup` from a `Prop41Data`, so Theorem A still consumes B1–B5 as fields.
* The `Ω_{Ã/B̃}` coherence argument showing the non-étale locus is a *proper closed
  subset* (the input to P4); only the finiteness consequence is proved.
* The Proposition of §5 that the induced dynamical system `(Ã, g̃)` is finite,
  surjective and projective on a normal variety.
* Example 4.4's conclusion `Branch(g) = ∅` *as a statement about a branch
  divisor*: the file proves the normalization facts that give it
  (`integralClosure_cuspAlg_eq_top` and `isIntegrallyClosed_polynomial`, so
  `B̃ = k[t] = A = Ã`), but there is no scheme-level `Branch(·)` in the model to
  state it against. Likewise `Crit(f) = V(u)` and `Branch(f) = V(x)` are not
  formalized: only the Jacobian `2u` is.
* Example 4.5's assertions that `Y` is normal and singular only at the vertex,
  and that `f` is étale away from it.
* §1's literature discussion, Remark 4.3 (formal-local picture), Remark 4.6,
  Remark 7.3 (the tame case), and Examples 6.3 (Dupont) and 7.1 beyond the
  concrete identities recorded in `Pcf/Examples/CharP.lean`.
* Dimension: Corollary 5.5's "at most `dim X` steps" is not modelled;
  `Pcf.pcf_descent` proves the statement for a chain of any length.

## F. Status of the formalization

Using the vocabulary of the formalization-evidence contract:

* `Pcf/Dynamics.lean`, `Pcf/Restriction.lean`, `Pcf/LocalModel.lean`,
  `Pcf/Examples/*` — **LEAN-PROVED**: they compile, and `#print axioms`
  reports only standard logical axioms.
* Theorem A (manuscript Theorem 5.1) — **CONDITIONAL** on A1–A5 and B1–B5.
  The dynamical and combinatorial half of the manuscript's proof is
  machine-checked; Theorem A's own route still consumes Proposition 4.1 as the
  field `PcfSetup.key`.
* Proposition 4.1 (manuscript §4) — **CONDITIONAL** on P1–P6 only. Its statement
  (1), (2) and (3) are proved in `Pcf/Geometry.lean` from Zariski–Nagata purity
  and Abhyankar's lemma, exactly as the manuscript argues.

This is not a machine verification of "PCF All the Way Down". It is a
machine-checked derivation of Theorem A, Corollary 5.2 and Corollary 5.5 from
Proposition 4.1 and the divisorial bookkeeping; a machine-checked derivation of
Proposition 4.1 itself from purity and Abhyankar's lemma; a machine-checked
derivation of the global form of purity from the local form; and machine-checked
proofs of the supporting examples. The remaining gap between the two is the
constructor that has not been written.
