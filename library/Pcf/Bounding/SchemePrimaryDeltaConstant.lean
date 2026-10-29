/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryResidueMap
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Local finiteness for a normalized purely inseparable cover

The chart normalization of `paper-p.tex`, Lemma `lem:pcf-transfer-charp`,
is finite. Its integral closure remains finite after localizing the base
at a divisor, including in the inseparable case.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- A finite integral closure stays finite over a localization of its base
when the containing field embeds the base. The top ring is the actual
integral closure of the localized ring in the same field. -/
theorem integralClosure_moduleFinite_localization
    (R Rₘ L : Type*) [CommRing R] [CommRing Rₘ] [Field L]
    [Algebra R Rₘ] [Algebra R L] [Algebra Rₘ L]
    [IsScalarTower R Rₘ L]
    (M : Submonoid R) [IsLocalization M Rₘ]
    (hinj : Function.Injective (algebraMap R L))
    (hzero : (0 : R) ∉ M)
    [Module.Finite R (integralClosure R L)] :
    Module.Finite Rₘ (integralClosure Rₘ L) := by
  let B := integralClosure R L
  let C := integralClosure Rₘ L
  have hBC : B ≤ C.restrictScalars R := by
    intro x hx
    exact hx.tower_top
  letI : Algebra B C := (Subalgebra.inclusion hBC).toRingHom.toAlgebra
  haveI : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hM : Algebra.algebraMapSubmonoid L M ≤ IsUnit.submonoid L := by
    rintro x ⟨m, hm, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hm0 : m = 0 := hinj (by simpa using hz)
    exact hzero (hm0 ▸ hm)
  letI : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.self hM
  letI : IsLocalization (Algebra.algebraMapSubmonoid B M) C :=
    IsLocalization.integralClosure M
  exact Module.Finite.of_isLocalization R B M

/-- Localizing at a prime gives a canonical algebra structure on the
containing field; finite integral closure survives this localization. -/
theorem integralClosure_moduleFinite_atPrime
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    (p : Ideal R) [p.IsPrime]
    (hinj : Function.Injective (algebraMap R L))
    [Module.Finite R (integralClosure R L)] :
    ∃ alg : Algebra (Localization.AtPrime p) L,
      letI := alg
      IsScalarTower R (Localization.AtPrime p) L ∧
        Module.Finite (Localization.AtPrime p)
          (integralClosure (Localization.AtPrime p) L) := by
  let Rp := Localization.AtPrime p
  have hunit : ∀ m : p.primeCompl, IsUnit (algebraMap R L m) := by
    intro ⟨m, hm⟩
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hm0 : m = 0 := hinj (by simpa using hz)
    exact hm (hm0 ▸ Ideal.zero_mem p)
  let liftMap : Rp →+* L := IsLocalization.lift hunit
  let alg : Algebra Rp L := liftMap.toAlgebra
  have hscalar : letI := alg; IsScalarTower R Rp L := by
    letI : Algebra Rp L := alg
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (IsLocalization.lift_eq hunit r).symm
  refine ⟨alg, hscalar, ?_⟩
  letI : Algebra Rp L := alg
  letI : IsScalarTower R Rp L := hscalar
  exact integralClosure_moduleFinite_localization R Rp L p.primeCompl hinj
    (by simp)

/-- Finite normalization of an integral scheme provides a finite integral
closure at every affine divisor prime, after localizing the base. -/
theorem schemeFieldExtensionNormalization_localIntegralClosure_moduleFinite
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [IsFinite (schemeFieldExtensionInclusion X L).fromNormalization]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    (p : Ideal Γ(X, U)) [p.IsPrime] :
    letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    ∃ alg : Algebra (Localization.AtPrime p) L,
      letI := alg
      IsScalarTower Γ(X, U) (Localization.AtPrime p) L ∧
        Module.Finite (Localization.AtPrime p)
          (integralClosure (Localization.AtPrime p) L) := by
  let R := Γ(X, U)
  let K := X.functionField
  letI : Algebra R L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap K L)).hom.toAlgebra
  letI : IsFractionRing R K :=
    functionField_isFractionRing_of_isAffineOpen X U U.2
  have hmap (a : R) : algebraMap R L a =
      algebraMap K L (algebraMap R K a) := by
    change (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap K L)).hom a =
      algebraMap K L ((X.germToFunctionField U).hom a)
    rfl
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [hmap] using hab
  haveI : Module.Finite R (integralClosure R L) :=
    schemeFieldExtensionNormalizationIntegralClosure_moduleFinite X L U U.2
  exact integralClosure_moduleFinite_atPrime R L p hinj

#print axioms integralClosure_moduleFinite_localization
#print axioms integralClosure_moduleFinite_atPrime
#print axioms schemeFieldExtensionNormalization_localIntegralClosure_moduleFinite

end
end Pcf
