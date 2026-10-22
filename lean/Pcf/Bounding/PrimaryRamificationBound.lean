/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryNormalizationFinite
public import Pcf.Bounding.PrimaryLocalDeltaConstant

/-!
# Prime-power ramification in a purely inseparable normalization

The fundamental identity at the unique prime of the actual finite
integral closure bounds its ramification index by the purely
inseparable function-field degree. This is the base-side estimate
used in `paper-p.tex`, Lemma `lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

universe u

set_option linter.style.haveILetI false

/-- At the unique maximal prime of the finite purely inseparable
normalization of a local normal curve, the ramification index divides
a power of the characteristic. The exponent comes from the actual
function-field degree, with no added module-finiteness premise. -/
theorem integralClosure_ramificationIdx_dvd_prime_power
    (k : Type u) [Field k] (pchar : ℕ) (hp : pchar.Prime)
    [CharP k pchar]
    (R : Type u) [CommRing R] [IsDedekindDomain R] [IsLocalRing R]
    [Algebra k R] [Algebra.FiniteType k R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type u) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L]
    (hmax : IsLocalRing.maximalIdeal R ≠ ⊥)
    (P : Ideal (integralClosure R L)) [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ a : ℕ,
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal R) P ∣
        pchar ^ a := by
  letI : CharP R pchar := charP_of_injective_algebraMap
    (algebraMap k R).injective pchar
  letI : CharP K pchar := charP_of_injective_algebraMap
    (IsFractionRing.injective R K) pchar
  letI : ExpChar K pchar :=
    (expChar_prime_iff K hp).mpr inferInstance
  let p := IsLocalRing.maximalIdeal R
  letI : CharP p.ResidueField pchar :=
    CharP.of_ringHom_of_ne_zero (algebraMap R p.ResidueField)
      pchar hp.ne_zero
  letI : ExpChar p.ResidueField pchar :=
    (expChar_prime_iff p.ResidueField hp).mpr inferInstance
  letI : Module.Finite R (integralClosure R L) :=
    finite_integralClosure_in_finite_extension k R K L
  letI := Localization.AtPrime.algebraOfLiesOver p P
  obtain ⟨a, ha⟩ := IsPurelyInseparable.finrank_eq_pow K L pchar
  have hδ := integralClosure_local_delta_eq_finrank_of_moduleFinite
    R K L pchar hmax P
  refine ⟨a, ?_⟩
  exact ⟨Field.finInsepDegree p.ResidueField P.ResidueField,
    (hδ.trans ha).symm⟩

#print axioms integralClosure_ramificationIdx_dvd_prime_power

end Pcf.Bounding.PrimaryFibres
