/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The integral closure of `R` in an algebra integral over `R_a`

Let `B` be an algebra over `R_a = R[1/a]` which is integral over `R_a` (for instance the ring of
functions of a finite étale cover `Y → Spec(R_a)`), and let `N` be the integral closure of `R` in
`B`, the ring of the normalization of `Spec R` in `Y`.  Then `B = N[1/a]`, so `N` is the integral
closure of `R` in `N[1/a]`.  This is the identification behind "the restriction of the
normalization `Y'` to `X ∖ D` is `Y`" in Stacks Tag `0EYH`.
-/

@[expose] public section

universe u

namespace Pcf.Stacks.SchemeLevel

variable {R : Type u} [CommRing R] (a : R) (Ra : Type u) [CommRing Ra] [Algebra R Ra]
  [IsLocalization.Away a Ra]
  (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]

/-- If `B` is integral over `R_a`, then `B` is the localization of the integral closure
`N` of `R` in `B` away from `a`. -/
theorem isLocalization_away_integralClosure [Algebra.IsIntegral Ra B] :
    IsLocalization.Away (algebraMap R (integralClosure R B) a) B := by
  have haB : IsUnit (algebraMap R B a) := by
    rw [IsScalarTower.algebraMap_apply R Ra B]
    exact (IsLocalization.Away.algebraMap_isUnit a).map _
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · exact haB
  · intro b
    obtain ⟨⟨m, k, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Submonoid.powers a) (Rₘ := Ra) b (Algebra.IsIntegral.isIntegral b)
    refine ⟨k, ⟨(a ^ k) • b, hm⟩, ?_⟩
    change b * algebraMap R B a ^ k = (a ^ k) • b
    rw [Algebra.smul_def, map_pow, mul_comm]
  · intro x y hxy
    refine ⟨0, ?_⟩
    simpa using Subtype.ext hxy

/-- If `B` is integral over `R_a`, then the integral closure of `R` in `B` is the integral
closure of `R` in its own localization away from `a`. -/
theorem isIntegralClosure_localizationAway_integralClosure [Algebra.IsIntegral Ra B] :
    IsIntegralClosure (integralClosure R B) R
      (Localization.Away (algebraMap R (integralClosure R B) a)) := by
  have := isLocalization_away_integralClosure a Ra B
  let N := integralClosure R B
  let f : B ≃ₐ[N] Localization.Away (algebraMap R N a) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R N a)) B _
  exact IsIntegralClosure.of_algEquiv N (f.restrictScalars R) fun x ↦ (f.commutes x).symm

end Pcf.Stacks.SchemeLevel
