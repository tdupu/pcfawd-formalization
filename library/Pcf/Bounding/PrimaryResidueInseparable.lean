/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFibres
public import Pcf.Bounding.CharPCoverDescent
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Integral

/-!
# Residue fields of a purely inseparable normalization

The proof of `latex/paper-p.tex`, Lemma `lem:pcf-transfer-charp`, uses
pure inseparability of the residue extension under the finite comparison
map. At a maximal prime this follows directly from the power-root property
of the integral closure.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

set_option linter.style.haveILetI false

/-- A power-root property for a ring extension descends to a purely
inseparable extension of residue fields at maximal ideals. -/
theorem residueField_isPurelyInseparable_of_pow_mem_base
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsMaximal]
    [P.LiesOver p] (q : ℕ) [ExpChar p.ResidueField q]
    (hroot : ∀ s : S, ∃ (n : ℕ) (r : R),
      s ^ (q ^ n) = algebraMap R S r) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    IsPurelyInseparable p.ResidueField P.ResidueField := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  apply (isPurelyInseparable_iff_pow_mem p.ResidueField q).2
  intro x
  obtain ⟨s, rfl⟩ := P.algebraMap_residueField_surjective x
  obtain ⟨n, r, hr⟩ := hroot s
  refine ⟨n, ⟨algebraMap R p.ResidueField r, ?_⟩⟩
  symm
  calc
    (algebraMap S P.ResidueField s) ^ (q ^ n) =
        algebraMap S P.ResidueField (s ^ (q ^ n)) := (map_pow _ _ _).symm
    _ = algebraMap S P.ResidueField (algebraMap R S r) := congrArg _ hr
    _ = algebraMap p.ResidueField P.ResidueField
          (algebraMap R p.ResidueField r) := by
            simp only [← IsScalarTower.algebraMap_apply R S P.ResidueField,
              ← IsScalarTower.algebraMap_apply R p.ResidueField P.ResidueField]

/-- The residue field above a maximal point of an actual purely
inseparable integral closure is purely inseparable over the base residue
field. This supplies the residue-field hypothesis in the local
`δ_ρ=q` calculation of `lem:pcf-transfer-charp`. -/
theorem integralClosure_residueField_isPurelyInseparable
    (R K L : Type*) [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsPurelyInseparable K L]
    (p : Ideal R) [p.IsMaximal]
    (P : Ideal (integralClosure R L)) [P.IsMaximal] [P.LiesOver p]
    (q : ℕ) [ExpChar K q] [ExpChar p.ResidueField q] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    IsPurelyInseparable p.ResidueField P.ResidueField := by
  exact residueField_isPurelyInseparable_of_pow_mem_base
    R (integralClosure R L) p P q
    (fun s => by
      obtain ⟨n, r, hr⟩ :=
        integralClosure_pow_mem_base (R := R) (K := K) (L := L) q s
      refine ⟨n, r, Subtype.val_injective ?_⟩
      simpa only [Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using hr)

/-- The local weighted degree of a finite purely inseparable integral
closure is its generic field degree. Here the top ring is the actual
integral closure, with the local Dedekind and finiteness conditions required
by the fundamental identity. -/
theorem integralClosure_local_delta_eq_finrank
    (R K L : Type*) [CommRing R] [IsDedekindDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    [Module.Finite R (integralClosure R L)]
    [IsDedekindDomain (integralClosure R L)]
    [IsLocalRing (integralClosure R L)]
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥)
    [(IsLocalRing.maximalIdeal (integralClosure R L)).LiesOver p]
    (q : ℕ) [ExpChar K q] [ExpChar p.ResidueField q] :
    let P := IsLocalRing.maximalIdeal (integralClosure R L)
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Ideal.ramificationIdx' p P *
      Field.finInsepDegree p.ResidueField P.ResidueField =
      Module.finrank K L := by
  let P := IsLocalRing.maximalIdeal (integralClosure R L)
  letI : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI := Localization.AtPrime.algebraOfLiesOver p P
  haveI : IsPurelyInseparable p.ResidueField P.ResidueField :=
    integralClosure_residueField_isPurelyInseparable R K L p P q
  exact local_purelyInseparable_delta_eq_finrank
    R (integralClosure R L) K L p hp0 this

#print axioms residueField_isPurelyInseparable_of_pow_mem_base
#print axioms integralClosure_residueField_isPurelyInseparable
#print axioms integralClosure_local_delta_eq_finrank

end Pcf.Bounding.PrimaryFibres
