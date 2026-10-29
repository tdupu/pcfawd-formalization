/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryResidueInseparable
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# The local purely inseparable integral closure

For a local normal Dedekind base, finite purely inseparable extension
of its fraction field has a local integral closure. When that closure
is module finite, its unique codimension-one local degree is the
generic purely inseparable degree. This removes localness and the
Dedekind hypothesis from the existing DVR calculation in
`paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

set_option linter.style.haveILetI false

/-- The actual integral closure over a local normal domain is local
when the fraction-field extension is purely inseparable. The proof
uses uniqueness of primes over a fixed prime and lying over. -/
theorem integralClosure_isLocalRing_of_purelyInseparable
    (R K L : Type*) [CommRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsPurelyInseparable K L]
    (pchar : ℕ) [ExpChar K pchar] :
    IsLocalRing (integralClosure R L) := by
  let B := integralClosure R L
  have hinj : Function.Injective (algebraMap R B) := by
    intro a b hab
    apply IsFractionRing.injective R K
    apply FaithfulSMul.algebraMap_injective K L
    have hL := congrArg (fun z : B => (z : L)) hab
    simpa only [Subalgebra.coe_algebraMap,
      ← IsScalarTower.algebraMap_apply R K L] using hL
  letI : FaithfulSMul R B :=
    (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  let p := IsLocalRing.maximalIdeal R
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) p
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨P, hPmax, ?_⟩
  intro Q hQmax
  letI : P.IsPrime := hPmax.isPrime
  letI : Q.IsPrime := hQmax.isPrime
  have hQunder : (Q.comap (algebraMap R B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (S := B) Q
  have hQp : Q.comap (algebraMap R B) = p :=
    IsLocalRing.eq_maximalIdeal hQunder
  have hPp : P.comap (algebraMap R B) = p :=
    (Ideal.liesOver_iff P p).mp hPover |>.symm
  exact (integralClosure_prime_comap_injective (R := R) (K := K)
    (L := L) pchar P Q (hPp.trans hQp.symm)).symm

/-- Module finiteness supplies the Dedekind structure of the actual
integral closure even for a purely inseparable fraction-field
extension. -/
theorem integralClosure_isDedekindDomain_of_moduleFinite
    (R K L : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L]
    [Module.Finite R (integralClosure R L)] :
    IsDedekindDomain (integralClosure R L) := by
  let B := integralClosure R L
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  haveI : Ring.DimensionLEOne B := inferInstance
  haveI : IsIntegrallyClosed B :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  exact { ‹IsNoetherianRing B›, ‹Ring.DimensionLEOne B›,
    ‹IsIntegrallyClosed B› with : IsDedekindDomain B }

/-- At the unique maximal prime of a finite purely inseparable
integral closure of a local Dedekind domain, the actual ramification
index times inseparable residue degree is the generic extension
degree. No local or Dedekind hypothesis on the integral closure is
needed: these are consequences of the extension and its finiteness. -/
theorem integralClosure_local_delta_eq_finrank_of_moduleFinite
    (R K L : Type*) [CommRing R] [IsDedekindDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    [Module.Finite R (integralClosure R L)]
    (pchar : ℕ) [ExpChar K pchar]
    [ExpChar (IsLocalRing.maximalIdeal R).ResidueField pchar]
    (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥)
    (P : Ideal (integralClosure R L)) [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal R)] :
    let p := IsLocalRing.maximalIdeal R
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Ideal.ramificationIdx' p P *
      Field.finInsepDegree p.ResidueField P.ResidueField =
      Module.finrank K L := by
  let B := integralClosure R L
  letI : IsLocalRing B :=
    integralClosure_isLocalRing_of_purelyInseparable R K L pchar
  letI : IsDedekindDomain B :=
    integralClosure_isDedekindDomain_of_moduleFinite R K L
  have hP : P = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal inferInstance
  subst P
  exact integralClosure_local_delta_eq_finrank R K L
    (IsLocalRing.maximalIdeal R) hp0 pchar

#print axioms integralClosure_isLocalRing_of_purelyInseparable
#print axioms integralClosure_isDedekindDomain_of_moduleFinite
#print axioms integralClosure_local_delta_eq_finrank_of_moduleFinite

end Pcf.Bounding.PrimaryFibres
