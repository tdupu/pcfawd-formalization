/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryLocalDeltaConstant
public import Pcf.Bounding.PrimaryFibreValuationSquare
public import Pcf.Ramification

/-!
# Tame indices in a purely inseparable local normalization

The local normalizations used in `paper-p.tex`, Lemma `lem:primary-fibres`,
are localizations of finite affine normalizations. Their stalk rings are
generally only essentially of finite type over the ground field. This
result therefore takes the module finiteness supplied by localization,
instead of assuming the local ring itself is of finite type.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

set_option linter.style.haveILetI false

/-- For the actual finite integral closure of a local normal curve in a
purely inseparable field extension, a ramification index prime to the
characteristic is one. The degree identity bounds it by a characteristic
power; no finite-type hypothesis on the local ring is used. -/
theorem integralClosure_ramificationIdx_eq_one_of_coprime
    (R K L : Type*) [CommRing R] [IsDedekindDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    [Module.Finite R (integralClosure R L)]
    (pchar : ℕ) (hp : pchar.Prime) [ExpChar K pchar]
    [ExpChar (IsLocalRing.maximalIdeal R).ResidueField pchar]
    (hmax : IsLocalRing.maximalIdeal R ≠ ⊥)
    (P : Ideal (integralClosure R L)) [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (htame : (Ideal.ramificationIdx' (IsLocalRing.maximalIdeal R) P).Coprime pchar) :
    Ideal.ramificationIdx' (IsLocalRing.maximalIdeal R) P = 1 := by
  let p := IsLocalRing.maximalIdeal R
  letI := Localization.AtPrime.algebraOfLiesOver p P
  obtain ⟨a, ha⟩ := IsPurelyInseparable.finrank_eq_pow K L pchar
  have hδ := integralClosure_local_delta_eq_finrank_of_moduleFinite
    R K L pchar hmax P
  have hdiv : Ideal.ramificationIdx' p P ∣ pchar ^ a :=
    ⟨Field.finInsepDegree p.ResidueField P.ResidueField,
      (hδ.trans ha).symm⟩
  exact Pcf.Ramification.index_eq_one_of_dvd_prime_pow hp
    (hp.coprime_iff_not_dvd.mp htame.symm) hdiv

#print axioms integralClosure_ramificationIdx_eq_one_of_coprime

/-- The valuation square in `lem:primary-fibres` gives index one for a
prime-to-characteristic original fibre once the altered fibre is reduced.
The indices are those of the four actual ring maps around the square. -/
theorem ramificationIdx_eq_one_of_primary_square
    {R S Rp T : Type*}
    [CommRing R] [CommRing S] [CommRing Rp] [CommRing T]
    [Algebra R S] [Algebra R Rp] [Algebra S T] [Algebra Rp T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R Rp T]
    [Module.Flat S T] [Module.Flat Rp T]
    (P : Ideal S) (Q : Ideal Rp) (E : Ideal T)
    [E.LiesOver P] [E.LiesOver Q]
    (pchar a : ℕ) (hp : pchar.Prime)
    (hbase : Q.ramificationIdx R ∣ pchar ^ a)
    (hreduced : E.ramificationIdx Rp = 1)
    (htame : (P.ramificationIdx R).Coprime pchar) :
    P.ramificationIdx R = 1 := by
  obtain ⟨b, _hb, hpower⟩ :=
    ramificationIdx_is_prime_power_of_square P Q E pchar a hp hbase hreduced
  apply Pcf.Ramification.index_eq_one_of_dvd_prime_pow hp
    (hp.coprime_iff_not_dvd.mp htame.symm)
  rw [hpower]

#print axioms ramificationIdx_eq_one_of_primary_square

end Pcf.Bounding.PrimaryFibres
