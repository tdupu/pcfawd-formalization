/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Pcf.Bounding.RegularLocalDomain

/-!
# Regular hypersurface sections in the purity induction

This file packages the elementary regular-local input used in the higher-dimensional branch of
Stacks Tag `0BMA`: in positive dimension one may choose an element of `m \ m²`, and quotienting
by such a minimal generator preserves regularity.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

open IsLocalRing

/-- A positive-dimensional regular local ring has a regular hypersurface section cut out by a
minimal generator of its maximal ideal. This is the regularity part of the hypersurface choice in
the induction of Stacks Tag `0BMA`. -/
theorem exists_regularLocalRing_quotient_minimalGenerator
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≠ 0) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧
      IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  obtain ⟨x, hx, hx2⟩ :=
    SetLike.exists_of_lt (IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hdim)
  have hspan : Ideal.span ({x} : Set R) ≠ ⊤ := Ideal.span_singleton_ne_top hx
  let _ : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hspan
  exact ⟨x, hx, hx2, isRegularLocalRing_quotient_minimalGenerator hx hx2⟩

/-- In dimension `d + 1`, the regular hypersurface section can be chosen with dimension exactly
`d`. This is the complete commutative-algebra hypersurface step used by the induction in Stacks
Tag `0BMA`. -/
theorem exists_regularLocalRing_quotient_of_ringKrullDim_eq_succ
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ)
    (hdim : ringKrullDim R = d + 1) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧
      IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) = d := by
  have hne : ringKrullDim R ≠ 0 := by
    rw [hdim]
    intro hzero
    have hnat : d + 1 = 0 := by exact_mod_cast hzero
    omega
  obtain ⟨x, hx, hx2, hregular⟩ :=
    exists_regularLocalRing_quotient_minimalGenerator R hne
  let _ : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := hregular
  exact ⟨x, hx, hx2, hregular,
    ringKrullDim_quotient_minimalGenerator_eq hx hx2 d hdim⟩

#print axioms exists_regularLocalRing_quotient_minimalGenerator
#print axioms exists_regularLocalRing_quotient_of_ringKrullDim_eq_succ

end Pcf.Stacks
