/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationFinite

/-!
# Finite integral closure in a finite function-field extension

Noether normalization and the characteristic-free polynomial-ring theorem
also make the integral closure of a finite-type domain finite in any finite
extension of its function field. This includes the Galois closure used for
specializing prime-to-`p` monodromy at a subvariety centre.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

universe u v w x

/-- A finite extension of the function field of a finite-type domain has
finite integral closure over the domain, in every characteristic. -/
theorem finite_integralClosure_of_finiteType_finiteExtension
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type x) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra R L] [IsScalarTower R K L] :
    Module.Finite R (integralClosure R L) := by
  obtain ⟨n, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin n) k
  letI : Algebra P R := f.toRingHom.toAlgebra
  haveI : FaithfulSMul P R := (faithfulSMul_iff_algebraMap_injective P R).mpr hf
  haveI : Module.Finite P R := hfin
  letI : Algebra P K := ((algebraMap R K).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower P R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul P K := .trans P R K
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  haveI : FiniteDimensional (FractionRing P) K :=
    Module.Finite.of_isLocalization P R P⁰
  letI : Algebra (FractionRing P) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing P) K)).toAlgebra
  haveI : IsScalarTower (FractionRing P) K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : FiniteDimensional (FractionRing P) L :=
    FiniteDimensional.trans (FractionRing P) K L
  letI : Algebra P L := ((algebraMap R L).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower P R L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower P K L := IsScalarTower.to₁₃₄ P R K L
  haveI : IsScalarTower P (FractionRing P) L :=
    IsScalarTower.to₁₂₄ P (FractionRing P) K L
  let C := integralClosure R L
  letI : Algebra P C := ((algebraMap R C).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower P R C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower P C L := IsScalarTower.to₁₃₄ P R C L
  haveI : IsIntegralClosure C P L := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro z
    constructor
    · intro hz
      exact ⟨⟨z, hz.tower_top⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact isIntegral_trans (R := P) (y : L) y.property
  have hfinite : Module.Finite P C :=
    TauCeti.IsIntegralClosure.finite_mvPolynomial k (FractionRing P) L C
  exact Module.Finite.of_restrictScalars_finite P R C

#print axioms finite_integralClosure_of_finiteType_finiteExtension

end

end Pcf
