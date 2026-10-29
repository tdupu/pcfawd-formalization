/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryLocalizedResidue

/-!
# The affine primary normalization degree at a divisor

The local purely inseparable degree formula from `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`, can be read on the global affine integral
closure chart. Ramification index and inseparable residue degree are
both unchanged by localization at the divisor.
-/

@[expose] public section

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- The weighted degree at a height-one prime of a finite primary
integral closure equals the generic field degree. The top ring is the
actual integral closure in `L`, localized at the base prime; its
module finiteness is derived from that of the global chart. -/
theorem integralClosure_delta_eq_genericDegree_atPrime
    (R Rₚ K L : Type*)
    [CommRing R] [CommRing Rₚ] [IsDedekindDomain Rₚ] [IsLocalRing Rₚ]
    [Field K] [Algebra Rₚ K] [IsFractionRing Rₚ K]
    [Field L] [Algebra K L] [Algebra Rₚ L] [IsScalarTower Rₚ K L]
    [Algebra R Rₚ] [Algebra R L] [IsScalarTower R Rₚ L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime Rₚ p]
    (hinj : Function.Injective (algebraMap R L))
    [Module.Finite R (integralClosure R L)]
    (pchar : ℕ) [ExpChar K pchar]
    [ExpChar (IsLocalRing.maximalIdeal Rₚ).ResidueField pchar]
    (hp0 : IsLocalRing.maximalIdeal Rₚ ≠ ⊥)
    (P : Ideal (integralClosure R L)) [P.IsPrime] [P.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    IsPurelyInseparable p.ResidueField P.ResidueField →
      P.ramificationIdx R *
        Field.finInsepDegree p.ResidueField P.ResidueField =
          Module.finrank K L := by
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
  let m := IsLocalRing.maximalIdeal Rₚ
  let Q := P.map (algebraMap B C)
  haveI : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver B p C P
  haveI : Q.LiesOver m := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rₚ C P
  haveI : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under Q
      (by rw [← Q.over_def m]; exact IsLocalRing.maximalIdeal.isMaximal Rₚ)
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI := Localization.AtPrime.algebraOfLiesOver m Q
  intro hpure
  have hram : Q.ramificationIdx Rₚ = P.ramificationIdx R :=
    integralClosure_ramificationIdx_localization R Rₚ L p hinj P
  have hres : Field.finInsepDegree p.ResidueField P.ResidueField =
      Field.finInsepDegree m.ResidueField Q.ResidueField :=
    finInsepDegree_localization_of_isPurelyInseparable
      R Rₚ B C p P hpure
  haveI : Module.Finite Rₚ C :=
    integralClosure_moduleFinite_localization R Rₚ L p.primeCompl hinj (by simp)
  haveI : IsDedekindDomain C :=
    Bounding.PrimaryFibres.integralClosure_isDedekindDomain_of_moduleFinite Rₚ K L
  have hinjRₚL : Function.Injective (algebraMap Rₚ L) := by
    intro a b hab
    apply IsFractionRing.injective Rₚ K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply Rₚ K L] using hab
  have hinjRₚC : Function.Injective (algebraMap Rₚ C) := by
    intro a b hab
    apply hinjRₚL
    have hL := congrArg (fun z : C => (z : L)) hab
    simpa only [Subalgebra.coe_algebraMap] using hL
  haveI : Module.IsTorsionFree Rₚ C :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjRₚC
  have hlocal : Ideal.ramificationIdx' m Q *
      Field.finInsepDegree m.ResidueField Q.ResidueField =
        Module.finrank K L :=
    integralClosure_local_delta_eq_genericDegree_after_localization
      R Rₚ K L p.primeCompl hinj (by simp) pchar hp0 Q
  rw [← hram, hres]
  simpa only [Ideal.ramificationIdx'_eq_ramificationIdx m Q hp0] using hlocal

#print axioms integralClosure_delta_eq_genericDegree_atPrime

end
end Pcf
