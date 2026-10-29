/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalization
public import Pcf.Vendor.TauCeti.RingTheory.IntegralClosure.MvPolynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Finiteness of normalization over an arbitrary field

Noether normalization reduces finiteness of integral closure for a finite-type
domain over any field to the characteristic-free finite-extension theorem for
polynomial rings, supplied by the vendored Tau Ceti proof. Applying this to
the coordinate rings in
Mathlib's relative-normalization construction proves that
`Palomar.normalizationMap A` is finite whenever `A` is integral and locally
of finite type over a field.
-/

@[expose] public section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

namespace Pcf

noncomputable section

/-- The integral closure of a finite-type domain over any field in its
fraction field is a finite module. -/
theorem finite_integralClosure_of_finiteType
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  obtain ⟨n, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin n) k
  let : Algebra P R := f.toRingHom.toAlgebra
  have : FaithfulSMul P R := (faithfulSMul_iff_algebraMap_injective P R).mpr hf
  have : Module.Finite P R := hfin
  let : Algebra P K := ((algebraMap R K).comp f.toRingHom).toAlgebra
  have : IsScalarTower P R K := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul P K := .trans P R K
  let : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  have : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  have : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P R P⁰
  let C := integralClosure R K
  let : Algebra P C := ((algebraMap R C).comp f.toRingHom).toAlgebra
  have : IsScalarTower P R C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P C K := IsScalarTower.to₁₃₄ P R C K
  have : IsIntegralClosure C P K := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx.tower_top⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact isIntegral_trans (R := P) (y : K) y.property
  have : Module.Finite P C :=
    TauCeti.IsIntegralClosure.finite_mvPolynomial k (FractionRing P) K C
  exact Module.Finite.of_restrictScalars_finite P R C

/-- On every nonempty affine open, the integral-closure ring used in the
generic-point normalization is finite over the original ring of sections. -/
theorem finite_schemeGenericIntegralClosure
    (A : Scheme.{u}) [IsIntegral A]
    (k : Type u) [Field k]
    (U : A.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [Algebra k Γ(A, U)] [Algebra.FiniteType k Γ(A, U)] :
    letI := ((schemeGenericInclusion A).app U).hom.toAlgebra
    Module.Finite Γ(A, U)
      (integralClosure Γ(A, U) Γ(Spec A.functionField, schemeGenericInclusion A ⁻¹ᵁ U)) := by
  let f := schemeGenericInclusion A
  let : Algebra Γ(A, U) Γ(Spec A.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have hgeneric : genericPoint A ∈ U :=
    ((genericPoint_spec A).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have htop : f ⁻¹ᵁ U = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem f (by simpa [f, schemeGenericInclusion])
  let e : Γ(Spec A.functionField, f ⁻¹ᵁ U) ≅ A.functionField :=
    (Spec A.functionField).presheaf.mapIso (eqToIso htop.symm).op ≪≫
      Scheme.ΓSpecIso A.functionField
  have he : f.app U ≫ e.hom = A.germToFunctionField U := by
    dsimp [f, schemeGenericInclusion, e]
    rw [Scheme.fromSpecStalk_app hgeneric]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp
  let ea : Γ(Spec A.functionField, f ⁻¹ᵁ U) ≃ₐ[Γ(A, U)] A.functionField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' r := congr($(he) r) }
  have : IsFractionRing Γ(A, U) A.functionField :=
    functionField_isFractionRing_of_isAffineOpen A U hU
  have : Module.Finite Γ(A, U) (integralClosure Γ(A, U) A.functionField) :=
    finite_integralClosure_of_finiteType k Γ(A, U) A.functionField
  exact Module.Finite.equiv ea.symm.mapIntegralClosure.toLinearEquiv

/-- The absolute normalization of an integral scheme whose affine coordinate
rings are finite-type over a field is finite. -/
theorem schemeGlobalNormalizationMap_isFinite_of_affineFiniteType
    (A : Scheme.{u}) [IsIntegral A]
    (k : Type u) [Field k]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    IsFinite (Palomar.normalizationMap A) := by
  constructor
  intro U hU
  by_cases hne : Nonempty U
  · let f := schemeGenericInclusion A
    let : Algebra Γ(A, U) Γ(Spec A.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    change (f.fromNormalization.app U).hom.Finite
    rw [f.fromNormalization_app hU, CommRingCat.hom_comp]
    apply RingHom.Finite.comp (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.finite
    let : Algebra k Γ(A, U) := inferInstanceAs (Algebra k Γ(A, (⟨U, hU⟩ : A.affineOpens)))
    have : Algebra.FiniteType k Γ(A, U) :=
      inferInstanceAs (Algebra.FiniteType k Γ(A, (⟨U, hU⟩ : A.affineOpens)))
    exact RingHom.finite_algebraMap.mpr (finite_schemeGenericIntegralClosure A k U hU)
  · have hbot : U = ⊥ := by
      ext x
      exact ⟨fun hx ↦ (hne ⟨⟨x, hx⟩⟩).elim, fun hx ↦ hx.elim⟩
    subst U
    have : Subsingleton Γ(Palomar.normalization A,
        Palomar.normalizationMap A ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstance : Subsingleton Γ(Palomar.normalization A, ⊥))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

/-- The absolute normalization map of an integral scheme locally of finite type
over any field is finite. In particular this applies to
integral schemes of finite type over that field. -/
theorem schemeGlobalNormalizationMap_isFinite
    (A : Scheme.{u}) [IsIntegral A]
    (k : Type u) [Field k]
    (s : A ⟶ Spec (.of k)) [LocallyOfFiniteType s] :
    IsFinite (Palomar.normalizationMap A) := by
  let φ (U : A.affineOpens) : k →+* Γ(A, U) :=
    (s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let (U : A.affineOpens) : Algebra k Γ(A, U) := (φ U).toAlgebra
  have (U : A.affineOpens) : Algebra.FiniteType k Γ(A, U) := by
    apply RingHom.finiteType_algebraMap.mp
    change (φ U).FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  exact schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k

#print axioms finite_integralClosure_of_finiteType
#print axioms finite_schemeGenericIntegralClosure
#print axioms schemeGlobalNormalizationMap_isFinite_of_affineFiniteType
#print axioms schemeGlobalNormalizationMap_isFinite

end

end Pcf
