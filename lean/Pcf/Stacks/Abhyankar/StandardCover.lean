/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Abhyankar
public import Pcf.LocalModel
public import Pcf.Stacks.Abhyankar.TameRamification

/-!
# The standard root cover

This file packages proved affine leaves of Stacks Project Example `0EYF` for
`C = R[z]/(z^e-u*a)`.  It proves finite freeness, gives the literal base-changed polynomial
after inverting `a`, proves that base change étale, and proves the codimension-one tame
clause under the characteristic-zero hypothesis used by PCFAWD.

The last theorem is intentionally named `_charZero`: Example `0EYF` itself only assumes
that `e` is invertible, and proving that sharper statement requires the exact computation
of every codimension-one ramification index as `e`.  Consequently no declaration in this
file is marked as the complete Stacks tag.
-/

@[expose] public section

universe u

open Polynomial

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]

/-- The equation of the standard root cover after base change to the complement of `V(a)`. -/
noncomputable abbrev localizedStandardPoly (u : Rˣ) (a : R) (e : ℕ) :
    (Localization.Away a)[X] :=
  (Pcf.LocalModel.localPoly u a e).map (algebraMap R (Localization.Away a))

/-- The image of `u*a` is a unit after localizing away from `a`. -/
noncomputable def localizedStandardUnit (u : Rˣ) (a : R) : (Localization.Away a)ˣ :=
  (((Units.isUnit u).map (algebraMap R (Localization.Away a))).mul
    (IsLocalization.Away.algebraMap_isUnit a)).unit

@[simp]
theorem localizedStandardUnit_val (u : Rˣ) (a : R) :
    (localizedStandardUnit u a : Localization.Away a) =
      algebraMap R (Localization.Away a) ((u : R) * a) := by
  rw [localizedStandardUnit, IsUnit.unit_spec]
  simp

/-- After inverting `a`, the standard ramified equation is literally a Kummer equation
with unit constant term. -/
theorem localizedStandardPoly_eq_kummerPoly (u : Rˣ) (a : R) (e : ℕ) :
    localizedStandardPoly u a e = Pcf.Kummer.kummerPoly (localizedStandardUnit u a) e := by
  simp [localizedStandardPoly, Pcf.LocalModel.localPoly, Pcf.Kummer.kummerPoly,
    localizedStandardUnit_val]

/-- The standard cover is étale after inverting the divisor equation, the second clause
of Stacks Example `0EYF`, stated on the explicit base-changed presentation. -/
theorem localizedStandardCover_etale (u : Rˣ) (a : R) {e : ℕ}
    (he : e ≠ 0) (heUnit : IsUnit (e : R)) :
    Algebra.Etale (Localization.Away a) (AdjoinRoot (localizedStandardPoly u a e)) := by
  rw [localizedStandardPoly_eq_kummerPoly]
  have heUnit' : IsUnit (e : Localization.Away a) := by
    simpa only [map_natCast] using
      heUnit.map (algebraMap R (Localization.Away a))
  exact Pcf.Kummer.etale_adjoinRoot_kummerPoly (localizedStandardUnit u a) he heUnit'

/-- The standard cover is finite over its base. -/
theorem standardCover_finite (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e) :
    Module.Finite R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) :=
  Pcf.LocalModel.finite_adjoinRoot u a he

/-- The standard cover is free over its base. -/
theorem standardCover_free (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e) :
    Module.Free R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) :=
  Pcf.LocalModel.free_adjoinRoot u a he

/-- The standard cover is free of rank `e` over a nontrivial base. -/
theorem standardCover_finrank [Nontrivial R] (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e) :
    Module.finrank R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) = e :=
  Pcf.LocalModel.finrank_adjoinRoot u a he

/-- Characteristic-zero form of the tame codimension-one clause of Example `0EYF`.

This does not compute the ramification index as `e`; it proves the exact tameness predicate
because the PCFAWD hypothesis makes every positive ramification index invertible in every
residue field, while finite residue extensions in characteristic zero are separable. -/
theorem standardCover_isTamelyRamifiedInCodimensionOne_charZero
    (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e)
    (hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) :
    IsTamelyRamifiedInCodimensionOneAlong R
      (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) a := by
  letI : Module.Finite R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) :=
    Pcf.LocalModel.finite_adjoinRoot u a he
  exact isTamelyRamifiedInCodimensionOneAlong_of_isUnit_natCast
    R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) hunit a

#print axioms localizedStandardCover_etale
#print axioms standardCover_free
#print axioms standardCover_isTamelyRamifiedInCodimensionOne_charZero

end Pcf.Stacks
