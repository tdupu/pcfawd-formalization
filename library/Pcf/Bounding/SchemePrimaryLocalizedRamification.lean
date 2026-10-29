/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryNormalizationResidue
public import Mathlib.RingTheory.Localization.AtPrime.Extension

/-!
# Ramification of a primary normalization after localization

The affine normalization chart of `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`, is an integral closure. Localizing that
integral closure at a divisor preserves the ramification index of its
prime. This is one part of the comparison between the actual scheme
divisor weight and the local degree calculation.
-/

@[expose] public section

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- Ramification at a prime of an actual integral closure is unchanged
when the base is localized at the contracted prime and the integral
closure is localized along with it. -/
theorem integralClosure_ramificationIdx_localization
    (R Rₚ L : Type*) [CommRing R] [CommRing Rₚ] [Field L]
    [Algebra R Rₚ] [Algebra R L] [Algebra Rₚ L]
    [IsScalarTower R Rₚ L]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    (hinj : Function.Injective (algebraMap R L))
    (P : Ideal (integralClosure R L)) [P.IsPrime] [P.LiesOver p] :
    let B := integralClosure R L
    let C := integralClosure Rₚ L
    let hBC : B ≤ C.restrictScalars R := fun _ hx => hx.tower_top
    letI : Algebra B C := (Subalgebra.inclusion hBC).toRingHom.toAlgebra
    (P.map (algebraMap B C)).ramificationIdx Rₚ = P.ramificationIdx R := by
  let B := integralClosure R L
  let C := integralClosure Rₚ L
  have hBC : B ≤ C.restrictScalars R := by
    intro x hx
    exact hx.tower_top
  letI : Algebra B C := (Subalgebra.inclusion hBC).toRingHom.toAlgebra
  haveI : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R Rₚ C := IsScalarTower.of_algebraMap_eq (fun r => by
    apply Subtype.val_injective
    simpa only [Subalgebra.coe_algebraMap] using
      (IsScalarTower.algebraMap_apply R Rₚ L r))
  have hM : Algebra.algebraMapSubmonoid L p.primeCompl ≤ IsUnit.submonoid L := by
    rintro x ⟨m, hm, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hm0 : m = 0 := hinj (by simpa using hz)
    exact hm (hm0 ▸ Ideal.zero_mem p)
  letI : IsLocalization (Algebra.algebraMapSubmonoid L p.primeCompl) L :=
    IsLocalization.self hM
  letI : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) C :=
    IsLocalization.integralClosure p.primeCompl
  exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rₚ C P

#print axioms integralClosure_ramificationIdx_localization

end
end Pcf
