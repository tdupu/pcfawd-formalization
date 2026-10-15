/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Lifting standard etale algebras across a quotient

This file proves the explicit algebraic lifting step used in the quotient comparison of Stacks
Tag `05WS`.  A standard etale pair over `R ⧸ I` need not admit coefficientwise lifts satisfying
its Bezout identity.  Instead, after lifting the monic polynomial and the coefficients in one
chosen Bezout identity, we replace the localization polynomial by a product whose reduction is a
positive power of the original localization polynomial.  Localizing at that product gives the
same standard etale algebra after base change.

No finality or strict-henselization comparison is asserted in this file.
-/

@[expose] public section

open Polynomial

universe u

namespace Pcf.Stacks.QuotientStandardEtale

variable {R : Type u} [CommRing R]

/-- A chosen coefficientwise lift of a polynomial over a quotient ring. -/
noncomputable def liftPolynomial (I : Ideal R) (p : (R ⧸ I)[X]) : R[X] :=
  (Polynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p).choose

@[simp]
theorem map_liftPolynomial (I : Ideal R) (p : (R ⧸ I)[X]) :
    (liftPolynomial I p).map (Ideal.Quotient.mk I) = p :=
  (Polynomial.map_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective p).choose_spec

/-- A chosen monic lift of the monic polynomial in a standard etale pair. -/
noncomputable def liftMonic (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) : R[X] :=
  (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective P.f) P.monic_f).choose

@[simp]
theorem map_liftMonic (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) :
    (liftMonic I P).map (Ideal.Quotient.mk I) = P.f :=
  (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective P.f)
      P.monic_f).choose_spec.1

theorem liftMonic_monic (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) :
    (liftMonic I P).Monic :=
  (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective P.f)
      P.monic_f).choose_spec.2.2

noncomputable def bezoutP₁ {I : Ideal R}
    (P : StandardEtalePair (R ⧸ I)) : (R ⧸ I)[X] :=
  P.cond.choose

noncomputable def bezoutP₂ {I : Ideal R}
    (P : StandardEtalePair (R ⧸ I)) : (R ⧸ I)[X] :=
  P.cond.choose_spec.choose

noncomputable def bezoutExponent {I : Ideal R}
    (P : StandardEtalePair (R ⧸ I)) : ℕ :=
  P.cond.choose_spec.choose_spec.choose

private theorem bezoutEquation {I : Ideal R} (P : StandardEtalePair (R ⧸ I)) :
    P.f.derivative * bezoutP₁ P + P.f * bezoutP₂ P = P.g ^ bezoutExponent P :=
  P.cond.choose_spec.choose_spec.choose_spec

/-- A standard etale pair over `R` lifting a pair over `R ⧸ I` up to replacing its
localization polynomial by a positive power after reduction. -/
noncomputable def liftPair (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) :
    StandardEtalePair R where
  f := liftMonic I P
  monic_f := liftMonic_monic I P
  g := liftPolynomial I P.g *
    ((liftMonic I P).derivative * liftPolynomial I (bezoutP₁ P) +
      liftMonic I P * liftPolynomial I (bezoutP₂ P))
  cond := ⟨liftPolynomial I (bezoutP₁ P) * liftPolynomial I P.g,
    liftPolynomial I (bezoutP₂ P) * liftPolynomial I P.g, 1, by ring⟩

@[simp]
theorem map_liftPair_f (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) :
    ((liftPair I P).map (Ideal.Quotient.mk I)).f = P.f := by
  simp [liftPair]

@[simp]
theorem map_liftPair_g (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) :
    ((liftPair I P).map (Ideal.Quotient.mk I)).g =
      P.g ^ (bezoutExponent P + 1) := by
  simp only [StandardEtalePair.map_g, liftPair, Polynomial.map_mul, Polynomial.map_add,
    map_liftPolynomial]
  rw [← Polynomial.derivative_map, map_liftMonic, bezoutEquation, pow_succ']

/-- The tautological standard-etale presentation of the ring attached to a standard pair. -/
noncomputable def pairPresentation (P : StandardEtalePair R) :
    StandardEtalePresentation R P.Ring where
  P := P
  x := P.X
  hasMap := P.hasMap_X
  lift_bijective := by
    simpa [StandardEtalePair.lift_X_left] using
      (Function.bijective_id : Function.Bijective (id : P.Ring → P.Ring))

/-- After quotient base change, the lifted standard etale pair defines the same algebra as the
original pair. -/
noncomputable def baseChangeEquiv (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) :
    ((liftPair I P).map (Ideal.Quotient.mk I)).Ring ≃ₐ[R ⧸ I] P.Ring := by
  let Q := (liftPair I P).map (Ideal.Quotient.mk I)
  have hf : Q.f = P.f := map_liftPair_f I P
  have hg : Q.g = P.g ^ (bezoutExponent P + 1) := map_liftPair_g I P
  have hQP : Q.HasMap P.X := by
    constructor
    · rw [hf]
      exact P.hasMap_X.1
    · rw [hg, map_pow]
      exact P.hasMap_X.2.pow _
  have hPQ : P.HasMap Q.X := by
    constructor
    · rw [← hf]
      exact Q.hasMap_X.1
    · apply (isUnit_pow_iff (Nat.succ_ne_zero (bezoutExponent P))).mp
      rw [← map_pow, ← hg]
      exact Q.hasMap_X.2
  let toHom : Q.Ring →ₐ[R ⧸ I] P.Ring := Q.lift P.X hQP
  let invHom : P.Ring →ₐ[R ⧸ I] Q.Ring := P.lift Q.X hPQ
  exact AlgEquiv.ofAlgHom toHom invHom
    (P.hom_ext (by
      simp only [AlgHom.comp_apply, toHom, invHom, StandardEtalePair.lift_X,
        AlgHom.id_apply]))
    (Q.hom_ext (by
      simp only [AlgHom.comp_apply, toHom, invHom, StandardEtalePair.lift_X]
      rfl))

/-- The tensor-product base change of the lifted standard-etale algebra is equivalent to the
original standard-etale algebra over the quotient. -/
noncomputable def tensorBaseChangeEquiv (I : Ideal R)
    (P : StandardEtalePair (R ⧸ I)) :
    TensorProduct R (R ⧸ I) (liftPair I P).Ring ≃ₐ[R ⧸ I] P.Ring :=
  ((pairPresentation (liftPair I P)).baseChange.equivRing).trans (baseChangeEquiv I P)

end Pcf.Stacks.QuotientStandardEtale
