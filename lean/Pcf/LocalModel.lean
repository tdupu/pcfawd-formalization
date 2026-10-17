/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The standard tame local model

This file formalizes the commutative-algebra core of Theorem `thm:bounding` of
*PCF All the Way Down* (`latex/paper.tex`).

The paper's `Strategy` section states that "the entire mechanism of *PCF all the way down*
is the elementary observation that restricting `O[z]/(z^e - u*a) → O` to `V(a)` gives
`O/(a) ≅ O/(a)`", and Step 3 of the proof of Theorem `thm:bounding` states that "in a standard
piece, the reduced preimage of `D` is `V(z)`, and `O[z]/(z^e - u*a, z) = O/(a)`, so
`V(z) → V(a)` is an isomorphism".  The Remark *Regularity of the source in the local model*
additionally records that the standard piece is free over the base with basis
`1, z, …, z^{e-1}` and that `z` is a nonzerodivisor when `a` is.

## Main definitions

* `Pcf.LocalModel.localPoly u a e` : the polynomial `X ^ e - C (u * a)` cutting out a
  standard piece of a tame cyclic cover.
* `Pcf.LocalModel.adjoinRootBasis` : the `R`-module basis `1, z, …, z ^ (e - 1)` of the standard piece.
* `Pcf.LocalModel.restrictionMap` : the restriction map `R/(a) → C/(z)` along the divisor,
  i.e. the algebraic form of `V(z) → V(a)`.
* `Pcf.LocalModel.restrictionEquiv` : that map packaged as an `R`-algebra isomorphism.

## Main results

* `Pcf.LocalModel.localPoly_monic` : `X ^ e - C (u * a)` is monic for `1 ≤ e`.
* `Pcf.LocalModel.free_adjoinRoot` / `Pcf.LocalModel.finite_adjoinRoot` / `Pcf.LocalModel.finrank_adjoinRoot` :
  the standard piece is a finite free `R`-module of rank `e`.
* `Pcf.LocalModel.quotientRootEquiv` : **the main result**, the `R`-algebra isomorphism
  `R[z]/(z ^ e - u * a, z) ≃ₐ[R] R/(a)`.  This is the statement
  `O[z]/(z^e - ua, z) = O/(a)` from Step 3 of Theorem `thm:bounding`.
* `Pcf.LocalModel.restrictionMap_bijective` : **the form of Step 3 that Step 4 uses**, namely
  that the restriction map `V(z) → V(a)` is an isomorphism *as a map*.
* `Pcf.LocalModel.root_mem_nonZeroDivisors` : `z` is a nonzerodivisor whenever `a` is.
* `Pcf.LocalModel.isNilpotent_root_mod_algebraMap` : `z` is nilpotent in `C/(a)`, the
  scheme-theoretic fibre of the cover over the divisor.  This carries no hypothesis on `e`
  and holds in the unramified cases `e = 0, 1` as well, so on its own it is *not* a
  ramification statement.
* `Pcf.LocalModel.root_ne_zero_mod_algebraMap` /
  `Pcf.LocalModel.isNilpotent_root_mod_algebraMap_ne_zero` : for `2 ≤ e` over a nontrivial
  ring `R` and with `a` a non-unit, that nilpotent is *nonzero*, so the scheme-theoretic
  fibre `C/(a)` is non-reduced.  This is the ramification of the *cover*, which the results
  above do not contradict; see the warning below.

## Ramification of the cover versus the restriction: a warning

The results here are about the map obtained by **restricting to the divisor**.  They say
nothing whatsoever about the ramification of the cover `R → C` itself, and must not be
quoted as if they did.

`Pcf.LocalModel.quotientRootEquiv` produces an isomorphism of the two quotient *rings*
`C/(z)` and `R/(a)`.  On its own, the bare existence of such an isomorphism carries no
information about how `R → C` ramifies.  The standard example: take `R = ℤ`, `a = 2`,
`u = 1`, `e = 2`, so that `C = ℤ[√2]` and `z = √2`.  Then indeed `C/(z) ≅ ℤ/2 ≅ R/(a)`, and
yet `2` is *totally ramified* in `ℤ[√2]`: as ideals `(2) = (√2) ^ 2`, so the ramification
index of the cover at that prime is `2`, not `1`.  An abstract isomorphism of the residue
rings is simply not a statement about ramification indices.

The manuscript agrees that the cover is ramified — that is the whole point of the standard
tame local model, whose ramification index along the divisor is `e`.  What is recorded here
is that the cover is ramified, in the form "the fibre is non-reduced":
`Pcf.LocalModel.isNilpotent_root_mod_algebraMap_ne_zero` says that for `2 ≤ e` over a
nontrivial ring `R` and with `a` a non-unit, the image of `z` in `C/(a)` is a **nonzero**
nilpotent, so the scheme-theoretic fibre of the cover over the divisor is non-reduced.  In
the example above this nilpotent is `√2 ∈ ℤ[√2]/(2)`.  (That the ramification index is
*exactly* `e` is a finer statement, and it is not formalized in this file.)

The weaker `Pcf.LocalModel.isNilpotent_root_mod_algebraMap` asserts nilpotency only, and it
must **not** be quoted as a ramification statement: it has no hypothesis on `e` whatsoever
and holds verbatim at `e = 0` and at `e = 1`, precisely the unramified cases — at `e = 1`
the element it exhibits as nilpotent is literally `0`, because `z = u * a` there.  It is
non-reducedness, not bare nilpotency, that distinguishes the ramified case, and that is
what the `_ne_zero` forms supply.  All three of their hypotheses are needed: for `e ≤ 1`,
for `a` a unit, and over the zero ring the image of `z` in `C/(a)` really is `0`.

What Step 4 of the proof of Theorem `thm:bounding` in `paper.tex` actually uses is a statement about
a *different* map: the restriction `g = f|_A`.  Its ramification index along the divisor
is `1` because the natural map `V(z) → V(a)` — the map induced by the structure map
`R → C`, not any abstractly chosen isomorphism — is an isomorphism.  That is
`Pcf.LocalModel.restrictionMap_bijective`, and that is the lemma to cite when the argument
needs "the restriction to the divisor is unramified".  Citing
`Pcf.LocalModel.quotientRootEquiv` for that purpose would be a genuine mathematical error.

## Implementation notes

Everything here is pure commutative algebra over an arbitrary commutative ring `R`; no
regularity, noetherian or excellence hypotheses are needed for these particular statements.
The divisor `D` of the manuscript is `V(a) = Spec (R / (a))` and the reduced preimage
`V(z)` is `Spec (C / (z))` for `C = R[z]/(z ^ e - u * a)`.

Note that the `Fin e`-indexed basis and the rank computation need `Nontrivial R`: over the
zero ring the polynomial `X ^ e - C (u * a)` is the zero polynomial, which is monic of
degree `0` rather than of degree `e`.  The `PowerBasis` (indexed by the degree of the
defining polynomial), freeness, finiteness, the main isomorphism and the nonzerodivisor
statement all hold over an arbitrary commutative ring.
-/

@[expose] public section

namespace Pcf.LocalModel

open Polynomial

variable {R : Type*} [CommRing R]

/-- The defining polynomial `X ^ e - C (u * a)` of a standard piece of a tame cyclic cover,
as in the local model of Theorem `thm:bounding` of `paper.tex` (`C = R[z]/(z ^ e - u * a)`). -/
noncomputable def localPoly (u : Rˣ) (a : R) (e : ℕ) : R[X] :=
  X ^ e - Polynomial.C ((u : R) * a)

/-- The defining polynomial of a standard piece is monic when `e ≥ 1`; this is the
"since the defining polynomial is monic" step of the Remark *Regularity of the source in
the local model* in `paper.tex`. -/
theorem localPoly_monic (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e) : (localPoly u a e).Monic :=
  monic_X_pow_sub_C _ (Nat.one_le_iff_ne_zero.mp he)

/-- Over a nontrivial ring the defining polynomial of a standard piece has degree exactly
`e`, the degree of the cover. -/
theorem localPoly_natDegree [Nontrivial R] (u : Rˣ) (a : R) (e : ℕ) :
    (localPoly u a e).natDegree = e :=
  natDegree_X_pow_sub_C

/-- Auxiliary form of `Pcf.LocalModel.root_pow_eq`. -/
private theorem root_pow_eq_aux (r : R) (e : ℕ) :
    AdjoinRoot.root (X ^ e - Polynomial.C r) ^ e
      = algebraMap R (AdjoinRoot (X ^ e - Polynomial.C r)) r := by
  have h : AdjoinRoot.mk (X ^ e - Polynomial.C r) (X ^ e - Polynomial.C r) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  simpa [AdjoinRoot.algebraMap_eq] using h

/-- The fundamental relation `z ^ e = u * a` in a standard piece `C = R[z]/(z ^ e - u * a)`
(Theorem `thm:bounding` of `paper.tex`). -/
theorem root_pow_eq (u : Rˣ) (a : R) (e : ℕ) :
    AdjoinRoot.root (localPoly u a e) ^ e
      = algebraMap R (AdjoinRoot (localPoly u a e)) ((u : R) * a) :=
  root_pow_eq_aux ((u : R) * a) e

section Free

variable (u : Rˣ) (a : R) {e : ℕ}

/-- The power basis `1, z, …, z ^ (d - 1)` (`d` the degree of the defining polynomial) of the
standard piece `C = R[z]/(z ^ e - u * a)`, from the Remark *Regularity of the source in the
local model* of `paper.tex`: "since the defining polynomial is monic, `C` is free over `R`
with basis `1, z, …, z^{e-1}`". -/
noncomputable def adjoinRootPowerBasis (he : 1 ≤ e) : PowerBasis R (AdjoinRoot (localPoly u a e)) :=
  AdjoinRoot.powerBasis' (localPoly_monic u a he)

/-- A standard piece `C = R[z]/(z ^ e - u * a)` is a free `R`-module
(Remark *Regularity of the source in the local model* of `paper.tex`). -/
theorem free_adjoinRoot (he : 1 ≤ e) : Module.Free R (AdjoinRoot (localPoly u a e)) :=
  Module.Free.of_basis (adjoinRootPowerBasis u a he).basis

/-- A standard piece `C = R[z]/(z ^ e - u * a)` is a finite `R`-module. -/
theorem finite_adjoinRoot (he : 1 ≤ e) : Module.Finite R (AdjoinRoot (localPoly u a e)) :=
  Module.Finite.of_basis (adjoinRootPowerBasis u a he).basis

/-- The `R`-module basis `1, z, …, z ^ (e - 1)` of the standard piece
`C = R[z]/(z ^ e - u * a)`, indexed by `Fin e`.  See the Remark
*Regularity of the source in the local model* of `paper.tex`. -/
noncomputable def adjoinRootBasis [Nontrivial R] (he : 1 ≤ e) :
    Module.Basis (Fin e) R (AdjoinRoot (localPoly u a e)) :=
  (adjoinRootPowerBasis u a he).basis.reindex (finCongr (localPoly_natDegree u a e))

/-- The `i`-th vector of `Pcf.LocalModel.adjoinRootBasis` is `z ^ i`: the basis really is
`1, z, …, z ^ (e - 1)`, as in the Remark *Regularity of the source in the local model*
of `paper.tex`. -/
@[simp]
theorem adjoinRootBasis_apply [Nontrivial R] (he : 1 ≤ e) (i : Fin e) :
    adjoinRootBasis u a he i = AdjoinRoot.root (localPoly u a e) ^ (i : ℕ) := by
  simp only [adjoinRootBasis, adjoinRootPowerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

/-- A standard piece `C = R[z]/(z ^ e - u * a)` is free of rank `e` over `R`:
the cover has degree `e`. -/
theorem finrank_adjoinRoot [Nontrivial R] (he : 1 ≤ e) :
    Module.finrank R (AdjoinRoot (localPoly u a e)) = e := by
  rw [Module.finrank_eq_card_basis (adjoinRootBasis u a he), Fintype.card_fin]

end Free

section Restriction

variable (u : Rˣ) (a : R) {e : ℕ}

/-- The `R`-algebra map `C = R[z]/(z ^ e - u * a) → R/(a)` sending `z` to `0`.  This is the
algebraic incarnation of the restriction of a standard piece to its branch divisor
(Step 3 of the proof of Theorem `thm:bounding` in `paper.tex`). -/
noncomputable def toQuotient (he : 1 ≤ e) :
    AdjoinRoot (localPoly u a e) →ₐ[R] R ⧸ Ideal.span ({a} : Set R) :=
  AdjoinRoot.liftAlgHom (localPoly u a e) (Algebra.ofId R (R ⧸ Ideal.span ({a} : Set R))) 0 <| by
    have h0 : ((u : R) * a) ∈ Ideal.span ({a} : Set R) :=
      Ideal.mem_span_singleton.mpr ⟨(u : R), mul_comm _ _⟩
    have hz : (0 : R ⧸ Ideal.span ({a} : Set R)) ^ e = 0 :=
      zero_pow (Nat.one_le_iff_ne_zero.mp he)
    simp only [localPoly, eval₂_sub, eval₂_X_pow, eval₂_C, hz, zero_sub, neg_eq_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h0

@[simp]
theorem toQuotient_mk (he : 1 ≤ e) (p : R[X]) :
    toQuotient u a he (AdjoinRoot.mk (localPoly u a e) p)
      = Ideal.Quotient.mk (Ideal.span ({a} : Set R)) (p.coeff 0) := by
  simp [toQuotient, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, eval₂_at_zero,
    Ideal.Quotient.algebraMap_eq]

@[simp]
theorem toQuotient_root (he : 1 ≤ e) :
    toQuotient u a he (AdjoinRoot.root (localPoly u a e)) = 0 := by
  rw [← AdjoinRoot.mk_X, toQuotient_mk]
  simp

/-- The image of `a` in a standard piece lies in the ideal `(z)`: this is the reason the
restriction map descends, and it is the identity `a = u⁻¹ * z ^ e` of Theorem `thm:bounding`
of `paper.tex`. -/
theorem algebraMap_mem_span_root (he : 1 ≤ e) :
    algebraMap R (AdjoinRoot (localPoly u a e)) a
      ∈ Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))) := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, (Nat.succ_pred_eq_of_pos he).symm⟩
  refine Ideal.mem_span_singleton.mpr ⟨algebraMap R _ ((u⁻¹ : Rˣ) : R)
    * AdjoinRoot.root (localPoly u a (d + 1)) ^ d, ?_⟩
  have h : AdjoinRoot.root (localPoly u a (d + 1)) ^ (d + 1)
      = algebraMap R (AdjoinRoot (localPoly u a (d + 1))) ((u : R) * a) :=
    root_pow_eq u a (d + 1)
  have hu : ((u⁻¹ : Rˣ) : R) * ((u : R) * a) = a := by
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  calc algebraMap R (AdjoinRoot (localPoly u a (d + 1))) a
      = algebraMap R _ (((u⁻¹ : Rˣ) : R) * ((u : R) * a)) := by rw [hu]
    _ = algebraMap R _ (((u⁻¹ : Rˣ) : R))
          * AdjoinRoot.root (localPoly u a (d + 1)) ^ (d + 1) := by rw [h, map_mul]
    _ = AdjoinRoot.root (localPoly u a (d + 1))
          * (algebraMap R _ (((u⁻¹ : Rˣ) : R))
              * AdjoinRoot.root (localPoly u a (d + 1)) ^ d) := by ring

/-- The `R`-algebra map `R/(a) → C/(z)` induced by the structure map `R → C`.
See Step 3 of the proof of Theorem `thm:bounding` of `paper.tex`. -/
noncomputable def fromQuotient (he : 1 ≤ e) :
    R ⧸ Ideal.span ({a} : Set R) →ₐ[R]
      AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))) :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R _).comp (Algebra.ofId R (AdjoinRoot (localPoly u a e)))) <| by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      simp only [AlgHom.comp_apply, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk, map_mul]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr
        (Ideal.mul_mem_right _ _ (algebraMap_mem_span_root u a he))

@[simp]
theorem fromQuotient_mk (he : 1 ≤ e) (r : R) :
    fromQuotient u a he (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) r)
      = Ideal.Quotient.mk _ (algebraMap R (AdjoinRoot (localPoly u a e)) r) :=
  rfl

/-- The `R`-algebra map `C/(z) → R/(a)` induced by `Pcf.LocalModel.toQuotient`. -/
noncomputable def toQuotientDescend (he : 1 ≤ e) :
    AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e)))
      →ₐ[R] R ⧸ Ideal.span ({a} : Set R) :=
  Ideal.Quotient.liftₐ _ (toQuotient u a he) <| by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, toQuotient_root, zero_mul]

@[simp]
theorem toQuotientDescend_mk (he : 1 ≤ e) (x : AdjoinRoot (localPoly u a e)) :
    toQuotientDescend u a he (Ideal.Quotient.mk _ x) = toQuotient u a he x :=
  rfl

/-- **Restriction to the branch divisor.**  For a standard piece
`C = R[z]/(z ^ e - u * a)` of a tame cyclic cover, with `u` a unit and `e ≥ 1`, the
reduced preimage `V(z)` of the branch divisor is isomorphic to the divisor `V(a)` itself:
`R[z]/(z ^ e - u * a, z) ≃ₐ[R] R/(a)`.

This is exactly the identity `O[z]/(z^e - ua, z) = O/(a)` of Step 3 of the proof of
Theorem `thm:bounding` in `paper.tex`, i.e. the "elementary observation" that the entire mechanism
of *PCF all the way down* rests on: restricting `O[z]/(z^e - ua) → O` to `V(a)` gives
`O/(a) ≅ O/(a)`. -/
noncomputable def quotientRootEquiv (he : 1 ≤ e) :
    (AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))))
      ≃ₐ[R] R ⧸ Ideal.span ({a} : Set R) :=
  AlgEquiv.ofAlgHom (toQuotientDescend u a he) (fromQuotient u a he)
    (by
      ext x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [AlgHom.comp_apply, fromQuotient_mk, toQuotientDescend_mk, AlgHom.commutes,
        AlgHom.coe_id, id_eq, Ideal.Quotient.algebraMap_eq])
    (by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
      obtain ⟨q, hq⟩ : (X : R[X]) ∣ p - Polynomial.C (p.coeff 0) := by
        rw [X_dvd_iff]; simp
      rw [AlgHom.comp_apply, toQuotientDescend_mk, toQuotient_mk, fromQuotient_mk,
        AlgHom.coe_id, id_eq, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      have hsub : AdjoinRoot.mk (localPoly u a e) (Polynomial.C (p.coeff 0))
            - AdjoinRoot.mk (localPoly u a e) p
          = -(AdjoinRoot.root (localPoly u a e) * AdjoinRoot.mk (localPoly u a e) q) := by
        rw [← map_sub, show Polynomial.C (p.coeff 0) - p = -(X * q) by rw [← hq]; ring,
          map_neg, map_mul, AdjoinRoot.mk_X]
      rw [hsub]
      exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

/-- **The restriction map `V(z) → V(a)`, algebraically.**  The `R`-algebra map
`R/(a) → C/(z)`, `C = R[z]/(z ^ e - u * a)`, induced by the structure map `R → C`.
On spectra this is the map `V(z) → V(a)` of Step 3 of the proof of Theorem `thm:bounding` in
`paper.tex`: the restriction `g = f|_A` of the cover to the (reduced preimage of the) branch
divisor.  It is a synonym for `Pcf.LocalModel.fromQuotient`, named for the role it plays in
Steps 3 and 4 of the proof.

Note that this is the map *along the divisor*, not the cover `R → C` itself; see the
section *Ramification of the cover versus the restriction* in the module documentation. -/
noncomputable def restrictionMap (he : 1 ≤ e) :
    R ⧸ Ideal.span ({a} : Set R) →ₐ[R]
      AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))) :=
  fromQuotient u a he

@[simp]
theorem restrictionMap_mk (he : 1 ≤ e) (r : R) :
    restrictionMap u a he (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) r)
      = Ideal.Quotient.mk _ (algebraMap R (AdjoinRoot (localPoly u a e)) r) :=
  rfl

/-- `Pcf.LocalModel.restrictionMap` is the inverse of the isomorphism
`Pcf.LocalModel.quotientRootEquiv` of Step 3 of Theorem `thm:bounding` in `paper.tex`. -/
theorem coe_quotientRootEquiv_symm (he : 1 ≤ e) :
    ⇑(quotientRootEquiv u a he).symm = ⇑(restrictionMap u a he) := by
  rw [quotientRootEquiv, AlgEquiv.ofAlgHom_symm]
  rfl

/-- **`V(z) → V(a)` is an isomorphism.**  The restriction map `R/(a) → C/(z)` induced by
`R → C = R[z]/(z ^ e - u * a)` is bijective, for `u` a unit and `e ≥ 1`.

This is the precise content of "so `V(z) → V(a)` is an isomorphism" in Step 3 of the proof
of Theorem `thm:bounding` of `paper.tex`, in the form used in Step 4: it is a statement about the
*specific map* `V(z) → V(a)`, not merely about the existence of some abstract isomorphism
between the two rings.  In particular it is this statement, and not
`Pcf.LocalModel.quotientRootEquiv` on its own, that says the restriction `g = f|_A` is
unramified along the divisor.  It says nothing about the ramification of the cover `R → C`,
which really does have ramification index `e`; see the module documentation. -/
theorem restrictionMap_bijective (he : 1 ≤ e) : Function.Bijective (restrictionMap u a he) := by
  rw [← coe_quotientRootEquiv_symm]
  exact (quotientRootEquiv u a he).symm.bijective

/-- **Restriction to the divisor is an isomorphism**, packaged as an `R`-algebra
isomorphism `R/(a) ≃ₐ[R] C/(z)` whose underlying map is
`Pcf.LocalModel.restrictionMap`.  Step 3 of the proof of Theorem `thm:bounding` of `paper.tex`. -/
noncomputable def restrictionEquiv (he : 1 ≤ e) :
    (R ⧸ Ideal.span ({a} : Set R)) ≃ₐ[R]
      AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))) :=
  AlgEquiv.ofBijective (restrictionMap u a he) (restrictionMap_bijective u a he)

@[simp]
theorem restrictionEquiv_apply (he : 1 ≤ e) (x : R ⧸ Ideal.span ({a} : Set R)) :
    restrictionEquiv u a he x = restrictionMap u a he x :=
  rfl

/-- The inverse of `Pcf.LocalModel.restrictionEquiv` is the map `C/(z) → R/(a)` sending
`z` to `0`, i.e. `Pcf.LocalModel.quotientRootEquiv`.  Step 3 of Theorem `thm:bounding` of
`paper.tex`. -/
theorem restrictionEquiv_symm_apply (he : 1 ≤ e)
    (x : AdjoinRoot (localPoly u a e) ⧸
      Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
        Set (AdjoinRoot (localPoly u a e)))) :
    (restrictionEquiv u a he).symm x = quotientRootEquiv u a he x := by
  rw [AlgEquiv.symm_apply_eq, restrictionEquiv_apply, ← coe_quotientRootEquiv_symm]
  exact ((quotientRootEquiv u a he).symm_apply_apply x).symm

end Restriction

section Ramification

variable (u : Rˣ) (a : R) {e : ℕ}

/-- `z ^ e` lies in the ideal generated by the image of `a`: in the *scheme-theoretic*
fibre of the cover over the divisor `V(a)`, the element `z` is nilpotent.  Together with
`Pcf.LocalModel.restrictionMap_bijective` this is the precise separation between the two
statements of Step 3 of Theorem `thm:bounding` of `paper.tex`: the *reduced* preimage `V(z)` maps
isomorphically to `V(a)`, while the *scheme-theoretic* fibre `C/(a)` of the cover carries a
nilpotent `z`, which for `e ≥ 2` is the non-reducedness expressing the ramification of the
cover. -/
theorem root_pow_mem_span_algebraMap :
    AdjoinRoot.root (localPoly u a e) ^ e
      ∈ Ideal.span ({algebraMap R (AdjoinRoot (localPoly u a e)) a} :
          Set (AdjoinRoot (localPoly u a e))) := by
  rw [root_pow_eq, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **`z` is nilpotent modulo `a`.**  In `C/(a)`, the fibre of the standard piece
`C = R[z]/(z ^ e - u * a)` over the divisor `V(a)`, the image of `z` is nilpotent (indeed
`z ^ e = u * a = 0` there).

This statement carries **no hypothesis on `e`**, and it is therefore *not* on its own a
statement about ramification: it holds verbatim at `e = 0` and at `e = 1`, precisely the
unramified cases, and at `e = 1` the element it exhibits as nilpotent is literally `0`,
because `z = u * a` there.  What witnesses ramification is the *nonvanishing* of this
nilpotent, which requires genuine hypotheses; see
`Pcf.LocalModel.root_ne_zero_mod_algebraMap` and
`Pcf.LocalModel.isNilpotent_root_mod_algebraMap_ne_zero`. -/
theorem isNilpotent_root_mod_algebraMap :
    IsNilpotent (Ideal.Quotient.mk
      (Ideal.span ({algebraMap R (AdjoinRoot (localPoly u a e)) a} :
        Set (AdjoinRoot (localPoly u a e))))
      (AdjoinRoot.root (localPoly u a e))) := by
  refine ⟨e, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (root_pow_mem_span_algebraMap u a)

/-- **The nilpotent is nonzero.**  For `2 ≤ e` over a nontrivial ring `R`, and with `a` a
non-unit, the image of `z` in `C/(a)` is nonzero, where `C = R[z]/(z ^ e - u * a)`.

Together with `Pcf.LocalModel.isNilpotent_root_mod_algebraMap` this exhibits a *nonzero*
nilpotent of `C/(a)`, so the scheme-theoretic fibre of the cover over the divisor `V(a)` is
non-reduced: the *cover* `R → C` really is ramified along the divisor, in contrast with its
restriction to the divisor, which is an isomorphism
(`Pcf.LocalModel.restrictionMap_bijective`).

The proof uses that `C` is free over `R` with basis `1, z, …, z ^ (e - 1)`
(`Pcf.LocalModel.adjoinRootBasis`): if the class of `z` vanished then `z = a * c` in `C`, and reading
off the coefficient of the basis vector `z` — a genuine basis vector, distinct from `1`,
precisely because `2 ≤ e` — gives `a * c₁ = 1`, making `a` a unit.

Every hypothesis is needed: for `e ≤ 1` and for `a` a unit the image of `z` in `C/(a)` is
genuinely `0`, and over the zero ring everything is `0`. -/
theorem root_ne_zero_mod_algebraMap [Nontrivial R] (he : 2 ≤ e) (ha : ¬ IsUnit a) :
    Ideal.Quotient.mk
        (Ideal.span ({algebraMap R (AdjoinRoot (localPoly u a e)) a} :
          Set (AdjoinRoot (localPoly u a e))))
        (AdjoinRoot.root (localPoly u a e)) ≠ 0 := by
  have he1 : 1 ≤ e := le_trans one_le_two he
  have hlt : (1 : ℕ) < e := he
  intro hzero
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hzero
  obtain ⟨c, hc⟩ := hzero
  have hroot : adjoinRootBasis u a he1 ⟨1, hlt⟩ = AdjoinRoot.root (localPoly u a e) := by
    rw [adjoinRootBasis_apply]; simp
  have h1 : (adjoinRootBasis u a he1).repr (AdjoinRoot.root (localPoly u a e)) ⟨1, hlt⟩ = 1 := by
    rw [← hroot, Module.Basis.repr_self, Finsupp.single_eq_same]
  have h2 : (adjoinRootBasis u a he1).repr
        (algebraMap R (AdjoinRoot (localPoly u a e)) a * c) ⟨1, hlt⟩
      = a * (adjoinRootBasis u a he1).repr c ⟨1, hlt⟩ := by
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact ha (IsUnit.of_mul_eq_one _ (by rw [← h2, ← hc, h1]))

/-- **The cover is ramified: `C/(a)` carries a nonzero nilpotent.**  For `2 ≤ e` over a
nontrivial ring `R`, and with `a` a non-unit, the image of `z` in the scheme-theoretic
fibre `C/(a)` of the standard piece `C = R[z]/(z ^ e - u * a)` over the divisor `V(a)` is a
nilpotent *and* is nonzero; equivalently, that fibre is non-reduced.

This is the ramification statement for the local model of Theorem `thm:bounding` of `paper.tex`, and
the companion to `Pcf.LocalModel.restrictionMap_bijective`: the *restriction to the divisor*
is an isomorphism, while the *cover* is ramified along the divisor.  (That the ramification
index is exactly `e` is a finer statement, not formalized here.)  See the module
documentation. -/
theorem isNilpotent_root_mod_algebraMap_ne_zero [Nontrivial R] (he : 2 ≤ e)
    (ha : ¬ IsUnit a) :
    IsNilpotent (Ideal.Quotient.mk
        (Ideal.span ({algebraMap R (AdjoinRoot (localPoly u a e)) a} :
          Set (AdjoinRoot (localPoly u a e))))
        (AdjoinRoot.root (localPoly u a e)))
      ∧ Ideal.Quotient.mk
        (Ideal.span ({algebraMap R (AdjoinRoot (localPoly u a e)) a} :
          Set (AdjoinRoot (localPoly u a e))))
        (AdjoinRoot.root (localPoly u a e)) ≠ 0 :=
  ⟨isNilpotent_root_mod_algebraMap u a, root_ne_zero_mod_algebraMap u a he ha⟩

end Ramification

section NonZeroDivisor

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- If `r` is a nonzerodivisor of `R` and `M` is a free `R`-module, then `r` acts injectively
on `M`.  This is the step that lets the manuscript's argument "`u a c = 0`, hence `c = 0`"
descend from `R` to `C`; see the Remark *Regularity of the source in the local model*
of `paper.tex`. -/
theorem eq_zero_of_smul_eq_zero_of_basis {ι : Type*} (b : Module.Basis ι R M) {r : R}
    (hr : r ∈ nonZeroDivisors R) {m : M} (h : r • m = 0) : m = 0 := by
  have hrepr : b.repr m = 0 := by
    ext i
    have hi : r * b.repr m i = 0 := by
      have := congrArg (fun x => b.repr x i) h
      simpa using this
    exact (mem_nonZeroDivisors_iff_left.mp hr) _ hi
  have := congrArg b.repr.symm hrepr
  simpa using this

variable (u : Rˣ) (a : R) {e : ℕ}

/-- **`z` is a nonzerodivisor.**  If `a` is a nonzerodivisor of `R` and `e ≥ 1`, then the
root `z` of `z ^ e - u * a` is a nonzerodivisor of the standard piece
`C = R[z]/(z ^ e - u * a)`.

This is the Remark *Regularity of the source in the local model* of `paper.tex`:
"as `a` is a nonzerodivisor, multiplication by `z` is injective: if `z c = 0`, then
`u a c = z^e c = 0`, hence `c = 0`" — the last step uses freeness of `C` over `R`. -/
theorem root_mem_nonZeroDivisors (he : 1 ≤ e) (ha : a ∈ nonZeroDivisors R) :
    AdjoinRoot.root (localPoly u a e) ∈ nonZeroDivisors (AdjoinRoot (localPoly u a e)) := by
  obtain ⟨d, hd⟩ : ∃ d, e = d + 1 := ⟨e - 1, (Nat.succ_pred_eq_of_pos he).symm⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro c hc
  have hua : (u : R) * a ∈ nonZeroDivisors R :=
    Submonoid.mul_mem _ (Units.isUnit u).mem_nonZeroDivisors ha
  have hsplit : AdjoinRoot.root (localPoly u a e) ^ e
      = AdjoinRoot.root (localPoly u a e) ^ d * AdjoinRoot.root (localPoly u a e) := by
    rw [← pow_succ, ← hd]
  have hpow : c * AdjoinRoot.root (localPoly u a e) ^ e = 0 := by
    rw [hsplit, ← mul_assoc, mul_right_comm, hc, zero_mul]
  rw [root_pow_eq] at hpow
  refine eq_zero_of_smul_eq_zero_of_basis (adjoinRootPowerBasis u a he).basis hua ?_
  rw [Algebra.smul_def, mul_comm]
  exact hpow

end NonZeroDivisor

end Pcf.LocalModel

#print axioms Pcf.LocalModel.localPoly_monic
#print axioms Pcf.LocalModel.adjoinRootBasis_apply
#print axioms Pcf.LocalModel.free_adjoinRoot
#print axioms Pcf.LocalModel.finrank_adjoinRoot
#print axioms Pcf.LocalModel.quotientRootEquiv
#print axioms Pcf.LocalModel.restrictionMap_bijective
#print axioms Pcf.LocalModel.root_mem_nonZeroDivisors
#print axioms Pcf.LocalModel.root_ne_zero_mod_algebraMap
#print axioms Pcf.LocalModel.isNilpotent_root_mod_algebraMap_ne_zero
