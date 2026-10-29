/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryLocalizedRamification

/-!
# Residue fields after localizing a normalization chart

This compares the residue fields of a prime above a base divisor with
those of the primes obtained by localizing the base and its finite
normalization. It is the residue-degree half of the local δ comparison
in `paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- Localizing a ring at a prime preserves its residue field. The map
used here is the canonical residue-field map of the localization, so
later algebra squares commute with the original ring maps. -/
noncomputable def residueFieldEquivOfLocalizationAtPrime
    (R Rₚ : Type*) [CommRing R] [CommRing Rₚ] [Algebra R Rₚ]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    p.ResidueField ≃+* (IsLocalRing.maximalIdeal Rₚ).ResidueField := by
  let m := IsLocalRing.maximalIdeal Rₚ
  haveI : m.LiesOver p := IsLocalization.AtPrime.liesOver_maximalIdeal Rₚ p
  have hp : p = m.comap (algebraMap R Rₚ) := Ideal.over_def m p
  let h : p.ResidueField →+* m.ResidueField :=
    Ideal.ResidueField.map p m (algebraMap R Rₚ) hp
  exact RingEquiv.ofBijective h
    ((RingHom.surjectiveOnStalks_of_isLocalization p.primeCompl Rₚ).residueFieldMap_bijective
      p m hp)

/-- Localizing an extension along a prime of the base preserves the
residue field at every prime of the extension lying above that prime. -/
noncomputable def residueFieldEquivOfLocalizationAbovePrime
    (R S Sₚ : Type*) [CommRing R] [CommRing S] [CommRing Sₚ]
    [Algebra R S] [Algebra S Sₚ]
    (p : Ideal R) [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    let Q := P.map (algebraMap S Sₚ)
    letI : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
    P.ResidueField ≃+* Q.ResidueField := by
  let Q := P.map (algebraMap S Sₚ)
  haveI : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
  have hP : P = Q.comap (algebraMap S Sₚ) :=
    (IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ
      ‹P.IsPrime› (Ideal.disjoint_primeCompl_of_liesOver P p)).symm
  let h : P.ResidueField →+* Q.ResidueField :=
    Ideal.ResidueField.map P Q (algebraMap S Sₚ) hP
  exact RingEquiv.ofBijective h
    ((RingHom.surjectiveOnStalks_of_isLocalization
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ).residueFieldMap_bijective
        P Q hP)

/-- The canonical residue-field equivalences for a localization of a
base ring and its extension commute with the residue-field extension. -/
theorem residueFieldEquivOfLocalization_square
    (R Rₚ S Sₚ : Type*)
    [CommRing R] [CommRing Rₚ] [CommRing S] [CommRing Sₚ]
    [Algebra R Rₚ] [Algebra R S] [Algebra S Sₚ]
    [Algebra R Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    let m := IsLocalRing.maximalIdeal Rₚ
    let Q := P.map (algebraMap S Sₚ)
    letI : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
    letI : Q.LiesOver m := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rₚ Sₚ P
    letI := Localization.AtPrime.algebraOfLiesOver p P
    letI := Localization.AtPrime.algebraOfLiesOver m Q
    (algebraMap m.ResidueField Q.ResidueField).comp
        (residueFieldEquivOfLocalizationAtPrime R Rₚ p).toRingHom =
      (residueFieldEquivOfLocalizationAbovePrime R S Sₚ p P).toRingHom.comp
        (algebraMap p.ResidueField P.ResidueField) := by
  let m := IsLocalRing.maximalIdeal Rₚ
  let Q := P.map (algebraMap S Sₚ)
  letI : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
  letI : Q.LiesOver m := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rₚ Sₚ P
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI := Localization.AtPrime.algebraOfLiesOver m Q
  let i := residueFieldEquivOfLocalizationAtPrime R Rₚ p
  let j := residueFieldEquivOfLocalizationAbovePrime R S Sₚ p P
  have hp : p = m.comap (algebraMap R Rₚ) := Ideal.over_def m p
  have hP : P = Q.comap (algebraMap S Sₚ) :=
    (IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ
      ‹P.IsPrime› (Ideal.disjoint_primeCompl_of_liesOver P p)).symm
  have hi : i.toRingHom = Ideal.ResidueField.map p m (algebraMap R Rₚ) hp := rfl
  have hj : j.toRingHom = Ideal.ResidueField.map P Q (algebraMap S Sₚ) hP := rfl
  apply IsFractionRing.ringHom_ext (A := R ⧸ p)
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk]
  rw [hi, hj]
  rw [← IsScalarTower.algebraMap_apply R p.ResidueField P.ResidueField]
  rw [IsScalarTower.algebraMap_apply R S P.ResidueField]
  simp only [Ideal.ResidueField.map_algebraMap]
  rw [← IsScalarTower.algebraMap_apply Rₚ m.ResidueField Q.ResidueField]
  rw [← IsScalarTower.algebraMap_apply R Rₚ Q.ResidueField,
    ← IsScalarTower.algebraMap_apply S Sₚ Q.ResidueField,
    ← IsScalarTower.algebraMap_apply R S Q.ResidueField]

/-- The inseparable residue degree of a purely inseparable extension
is unchanged by localization at a prime of the base. -/
theorem finInsepDegree_localization_of_isPurelyInseparable
    (R Rₚ S Sₚ : Type*)
    [CommRing R] [CommRing Rₚ] [CommRing S] [CommRing Sₚ]
    [Algebra R Rₚ] [Algebra R S] [Algebra S Sₚ]
    [Algebra R Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    let m := IsLocalRing.maximalIdeal Rₚ
    let Q := P.map (algebraMap S Sₚ)
    letI : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
    letI : Q.LiesOver m := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rₚ Sₚ P
    letI := Localization.AtPrime.algebraOfLiesOver p P
    letI := Localization.AtPrime.algebraOfLiesOver m Q
    IsPurelyInseparable p.ResidueField P.ResidueField →
      Field.finInsepDegree p.ResidueField P.ResidueField =
        Field.finInsepDegree m.ResidueField Q.ResidueField := by
  dsimp only
  let m := IsLocalRing.maximalIdeal Rₚ
  let Q := P.map (algebraMap S Sₚ)
  letI : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
  letI : Q.LiesOver m := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rₚ Sₚ P
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI := Localization.AtPrime.algebraOfLiesOver m Q
  intro hpure
  letI : IsPurelyInseparable p.ResidueField P.ResidueField := hpure
  exact (finInsepDegree_eq_of_ringEquiv_square_of_purelyInseparable
    (residueFieldEquivOfLocalizationAtPrime R Rₚ p)
    (residueFieldEquivOfLocalizationAbovePrime R S Sₚ p P)
    (residueFieldEquivOfLocalization_square R Rₚ S Sₚ p P)).2

#print axioms residueFieldEquivOfLocalizationAtPrime
#print axioms residueFieldEquivOfLocalizationAbovePrime
#print axioms residueFieldEquivOfLocalization_square
#print axioms finInsepDegree_localization_of_isPurelyInseparable

end
end Pcf
