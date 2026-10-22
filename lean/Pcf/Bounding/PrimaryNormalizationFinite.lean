/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryNormalizationUniversallyInjective
public import Pcf.Bounding.GlobalNormalizationFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finiteness of purely inseparable normalization over a field

Noether normalization and finite-extension finiteness show that the
integral closure of a finite-type normal domain in a finite function-field
extension is finite. The extension need not be separable. Combined with
the root-property result, this gives the finite radicial normalization
used in `paper-p.tex`, Lemma `lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

universe u v w z

noncomputable section

set_option linter.style.haveILetI false

/-- The actual integral closure in a finite extension of the fraction
field of a finite-type domain over a field is finite over that domain,
without a separability assumption. -/
theorem finite_integralClosure_in_finite_extension
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R]
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type z) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] :
    Module.Finite R (integralClosure R L) := by
  obtain ⟨n, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin n) k
  letI : Algebra P R := f.toRingHom.toAlgebra
  haveI : FaithfulSMul P R :=
    (faithfulSMul_iff_algebraMap_injective P R).mpr hf
  letI : Module.Finite P R := hfin
  letI : Algebra P K := ((algebraMap R K).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower P R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul P K := .trans P R K
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K :=
    FractionRing.isScalarTower_liftAlgebra P K
  haveI : FiniteDimensional (FractionRing P) K :=
    Module.Finite.of_isLocalization P R P⁰
  letI : Algebra (FractionRing P) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing P) K)).toAlgebra
  haveI : IsScalarTower (FractionRing P) K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : FiniteDimensional (FractionRing P) L := Module.Finite.trans K L
  letI : Algebra P L := ((algebraMap K L).comp (algebraMap P K)).toAlgebra
  haveI : IsScalarTower P K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower P R L := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    change algebraMap K L (algebraMap P K x) =
      algebraMap R L (algebraMap P R x)
    rw [IsScalarTower.algebraMap_apply P R K,
      IsScalarTower.algebraMap_apply R K L])
  haveI : IsScalarTower P (FractionRing P) L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact congrArg (algebraMap K L)
        (IsScalarTower.algebraMap_apply P (FractionRing P) K x))
  let C := integralClosure R L
  letI : Algebra P C := ((algebraMap R C).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower P R C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower P C L := IsScalarTower.to₁₃₄ P R C L
  haveI : IsIntegralClosure C P L := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx.tower_top⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact isIntegral_trans (R := P) (y : L) y.property
  haveI : Module.Finite P C :=
    TauCeti.IsIntegralClosure.finite_mvPolynomial k (FractionRing P) L C
  exact Module.Finite.of_restrictScalars_finite P R C

/-- For a normal finite-type domain, the affine normalization in a finite
purely inseparable function-field extension is a finite scheme morphism. -/
theorem integralClosure_specMap_isFinite
    (k : Type u) [Field k]
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type u) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] :
    IsFinite
      (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr
    (finite_integralClosure_in_finite_extension k R K L)

/-- In positive characteristic, the normalization in a finite purely
inseparable function-field extension is finite, surjective and radicial
over a normal finite-type affine base. -/
theorem integralClosure_specMap_finite_radicial
    (k : Type u) [Field k] (p : ℕ) (hp : p.Prime) [CharP k p]
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type u) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] :
    let f := Spec.map
      (CommRingCat.ofHom (algebraMap R (integralClosure R L)))
    IsFinite f ∧ UniversallyInjective f ∧ Surjective f := by
  letI : CharP R p := charP_of_injective_algebraMap
    (algebraMap k R).injective p
  letI : CharP K p := charP_of_injective_algebraMap
    (IsFractionRing.injective R K) p
  letI : ExpChar K p := (expChar_prime_iff K hp).mpr inferInstance
  refine ⟨integralClosure_specMap_isFinite k R K L,
    integralClosure_universallyInjective_specMap R K L p hp, ?_⟩
  constructor
  exact (integralClosure_isHomeomorph_comap (R := R) (K := K)
    (L := L) p).surjective

#print axioms finite_integralClosure_in_finite_extension
#print axioms integralClosure_specMap_isFinite
#print axioms integralClosure_specMap_finite_radicial

end

end Pcf.Bounding.PrimaryFibres
