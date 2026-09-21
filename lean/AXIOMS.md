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

These are proved in the manuscript or quoted from the literature there, and
are hypotheses in Lean. Each is a field of a structure, listed with the
declaration that carries it.

| ID | Lean field | Statement assumed | Manuscript / literature source |
| --- | --- | --- | --- |
| B1 | `DivDyn.step_surjective` | Lying over: every prime is the image of a prime. Proved in the manuscript from lying-over, going-down for a finite extension of a normal domain, and incomparability. | Proof of Lemma 3.2; Stacks Tag 00HS / 00H8 |
| B2 | `DivDyn.branch_finite'` | The branch divisor has finitely many components. Proved in the manuscript from coherence of `Ω` and Noetherianness. | §2, paragraph after Definition 2.3 |
| B3 | `PcfSetup.sing_finite` | `Sing(Y) ∩ B` and `Sing(B)` are proper closed in `B`, hence contain finitely many primes of `B`. | Proposition 4.1(1) |
| B4 | `PcfSetup.meets_finite` | `B ∩ Z` is proper closed in `B` for `Z` a union of primes `≠ B`, hence contains finitely many primes of `B`. | Proposition 4.1(1) |
| B5 | `PcfSetup.key` | **Proposition 4.1(2), the key proposition**, applied to every iterate `fᵐ`: a prime `Q'` of `B` whose generic point lies outside `Sing(Y)`, outside `Sing(B)` and outside `Z` is not a branch prime of `g = f|_A`. | Proposition 4.1(2); proved there from Zariski–Nagata purity (Stacks Tag 0BMB) and Abhyankar's lemma for a regular divisor (Stacks Tags 0EYF, 0EYG; SGA 1 Exp. XIII Prop. 5.2) |

B5 is the whole geometric content of §4. Its proof — Steps 1–4 of the
manuscript — is *not* formalized, with one exception: the algebraic core of
Step 3 is proved outright in `Pcf/LocalModel.lean` (see §D below).

**Non-vacuity.** B1–B5 are simultaneously satisfiable with nontrivial branch
data: `Pcf/Examples/Squaring.lean` builds an explicit `PcfSetup` whose `key`
field is *proved*, not assumed, and derives the conclusion of Theorem A on it
by applying `Pcf.PcfSetup.res_pcf`.

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
* The proof of Proposition 4.1: the purity step (Step 1), the Abhyankar step
  (Step 2), the regularity remark, and the strict-henselization/étale-base-change
  invariance of ramification indices (Step 4).
* The finiteness-of-`Branch` argument via `Ω_{Ã/B̃}` (assumed as B2).
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
  machine-checked; the geometric half (Proposition 4.1) is assumed.

This is not a machine verification of "PCF All the Way Down". It is a
machine-checked derivation of Theorem A, Corollary 5.2 and Corollary 5.5 from
Proposition 4.1 and the divisorial bookkeeping, together with machine-checked
proofs of the supporting examples.
