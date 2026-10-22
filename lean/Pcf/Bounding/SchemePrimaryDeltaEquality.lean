/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryDeltaConstant

/-!
# The local degree of a finite primary normalization after localization

This packages the finite normalization chart, localization of integral
closure, and the local Dedekind degree formula at a divisor. The final
scheme `schemeDivisorDelta` comparison additionally needs invariance of
ramification and residue degree under this localization.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- A finite purely inseparable integral closure has local weighted degree
equal to the generic field degree after localizing a finite normalization
chart at a divisor. Finiteness of the localized integral closure is proved
from finiteness of the original chart. -/
theorem integralClosure_local_delta_eq_genericDegree_after_localization
    (R Rₘ K L : Type*)
    [CommRing R] [CommRing Rₘ] [IsDedekindDomain Rₘ] [IsLocalRing Rₘ]
    [Field K] [Algebra Rₘ K] [IsFractionRing Rₘ K]
    [Field L] [Algebra K L] [Algebra Rₘ L] [IsScalarTower Rₘ K L]
    [Algebra R Rₘ] [Algebra R L] [IsScalarTower R Rₘ L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (M : Submonoid R) [IsLocalization M Rₘ]
    (hinj : Function.Injective (algebraMap R L))
    (hzero : (0 : R) ∉ M)
    [Module.Finite R (integralClosure R L)]
    (pchar : ℕ) [ExpChar K pchar]
    [ExpChar (IsLocalRing.maximalIdeal Rₘ).ResidueField pchar]
    (hp0 : IsLocalRing.maximalIdeal Rₘ ≠ ⊥)
    (P : Ideal (integralClosure Rₘ L)) [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal Rₘ)] :
    let p := IsLocalRing.maximalIdeal Rₘ
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Ideal.ramificationIdx' p P *
      Field.finInsepDegree p.ResidueField P.ResidueField =
        Module.finrank K L := by
  letI : Module.Finite Rₘ (integralClosure Rₘ L) :=
    integralClosure_moduleFinite_localization R Rₘ L M hinj hzero
  exact Bounding.PrimaryFibres.integralClosure_local_delta_eq_finrank_of_moduleFinite
    Rₘ K L pchar hp0 P

/-- The power-root condition on an integral-closure chart transfers through
its canonical algebra equivalence with the scheme's affine sections. -/
theorem pow_mem_base_of_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (pchar : ℕ)
    (hroot : ∀ t : T, ∃ (n : ℕ) (r : R),
      t ^ (pchar ^ n) = algebraMap R T r) :
    ∀ s : S, ∃ (n : ℕ) (r : R),
      s ^ (pchar ^ n) = algebraMap R S r := by
  intro s
  obtain ⟨n, r, hr⟩ := hroot (e s)
  refine ⟨n, r, e.injective ?_⟩
  simpa only [map_pow, AlgEquiv.commutes] using hr

#print axioms integralClosure_local_delta_eq_genericDegree_after_localization
#print axioms pow_mem_base_of_algEquiv

end
end Pcf
