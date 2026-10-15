/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientRefinement

/-!
# Finality of quotient base change on pointed etale neighbourhoods

This file supplies the morphism-equalization half of finality for quotient base change.  Given two
pointed maps into a quotient-base-changed stage, the diagonal idempotent of their source cuts out
their equalizer.  The complement of that idempotent is lifted to the original stage and inverted;
after quotient base change the idempotent vanishes, so the two maps agree.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Two pointed maps into the quotient base change of one stage are equalized after refining that
stage over the original ring. -/
theorem exists_quotientBaseChange_equalizing_refinement (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    let _ : IsScalarTower R (R ⧸ I) Ω :=
      IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
    ∀ {X : PointedEtaleNeighborhood (R ⧸ I) Ω}
      {Y : PointedEtaleNeighborhood R Ω}
      (s t : X ⟶ baseChangeObj (R := R) (S := R ⧸ I) Y),
      ∃ (Y' : PointedEtaleNeighborhood R Ω) (h : Y ⟶ Y'),
        s ≫ baseChangeMap (S := R ⧸ I) h =
          t ≫ baseChangeMap (S := R ⧸ I) h := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  change ∀ {X : PointedEtaleNeighborhood (R ⧸ I) Ω}
    {Y : PointedEtaleNeighborhood R Ω}
    (s t : X ⟶ baseChangeObj (R := R) (S := R ⧸ I) Y),
    ∃ (Y' : PointedEtaleNeighborhood R Ω) (h : Y ⟶ Y'),
      s ≫ baseChangeMap (S := R ⧸ I) h =
        t ≫ baseChangeMap (S := R ⧸ I) h
  intro X Y s t
  let J := KaehlerDifferential.ideal (R ⧸ I) X
  have hJ : IsIdempotentElem J :=
    (Ideal.cotangent_subsingleton_iff J).mp (by
      change Subsingleton Ω[X⁄(R ⧸ I)]
      infer_instance)
  obtain ⟨e, he, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg J
      (KaehlerDifferential.ideal_fg (R ⧸ I) X)).mp hJ
  let p : X ⊗[R ⧸ I] X →ₐ[R ⧸ I]
      baseChangeObj (R := R) (S := R ⧸ I) Y :=
    Algebra.TensorProduct.productMap s.hom t.hom
  let d : baseChangeObj (R := R) (S := R ⧸ I) Y := p e
  have hd : IsIdempotentElem d := by
    change d * d = d
    simp only [d, ← map_mul, he.eq]
  have hpcomp : (baseChangeObj (R := R) (S := R ⧸ I) Y).point.comp p =
      X.point.comp (Algebra.TensorProduct.lmul' (R ⧸ I)) := by
    ext x
    · simpa [p] using DFunLike.congr_fun s.point_comp x
    · simpa [p] using DFunLike.congr_fun t.point_comp x
  have heJ : e ∈ J := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self e
  have hlmule : Algebra.TensorProduct.lmul' (R ⧸ I) e = 0 := by
    rw [RingHom.mem_ker] at heJ
    exact heJ
  have hpointd : (baseChangeObj (R := R) (S := R ⧸ I) Y).point d = 0 := by
    change ((baseChangeObj (R := R) (S := R ⧸ I) Y).point.comp p) e = 0
    rw [hpcomp]
    simp [hlmule]
  let E : baseChangeObj (R := R) (S := R ⧸ I) Y ≃ₐ[R ⧸ I]
      TensorProduct R (R ⧸ I) Y :=
    ofEtaleAlgebraEquiv (TensorProduct R (R ⧸ I) Y)
      (baseChangePoint (R := R) (S := R ⧸ I) Y)
  obtain ⟨y, hy⟩ : ∃ y : Y, (1 : R ⧸ I) ⊗ₜ[R] y = E (1 - d) := by
    obtain ⟨z, hz⟩ := (quotientStageEquiv I Y).surjective (E (1 - d))
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨y, (quotientStageEquiv_mk I Y y).trans hz⟩
  have hpointy : Y.point y = 1 := by
    calc
      Y.point y = baseChangePoint (R := R) (S := R ⧸ I) Y
          ((1 : R ⧸ I) ⊗ₜ[R] y) := by simp [baseChangePoint]
      _ = baseChangePoint (R := R) (S := R ⧸ I) Y (E (1 - d)) :=
        congrArg _ hy
      _ = (baseChangeObj (R := R) (S := R ⧸ I) Y).point (1 - d) := by rfl
      _ = 1 := by rw [map_sub, map_one, hpointd, sub_zero]
  let L := Localization.Away y
  let pointL : L →ₐ[R] Ω := IsLocalization.Away.liftAlgHom y
    (f := Y.point) (hpointy ▸ isUnit_one)
  let q : Y →ₐ[R] L := IsScalarTower.toAlgHom R Y L
  have hpointLq : pointL.comp q = Y.point := by
    ext z
    simp [pointL, q]
  let Y' := ofEtaleAlgebra L pointL
  let h : Y ⟶ Y' := homToOfEtaleAlgebra L pointL q hpointLq
  let E' : Y' ≃ₐ[R] L := ofEtaleAlgebraEquiv L pointL
  let m : TensorProduct R (R ⧸ I) Y →ₐ[R ⧸ I]
      TensorProduct R (R ⧸ I) Y' :=
    Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I)) h.hom
  let k : baseChangeObj (R := R) (S := R ⧸ I) Y →ₐ[R ⧸ I]
      TensorProduct R (R ⧸ I) Y' := m.comp E.toAlgHom
  have hyunit : IsUnit (h.hom y) := by
    change IsUnit (E'.symm (q y))
    exact (IsLocalization.Away.algebraMap_isUnit y (S := L)).map E'.symm.toRingHom
  have hcompunit : IsUnit (k (1 - d)) := by
    have hu : IsUnit ((1 : R ⧸ I) ⊗ₜ[R] h.hom y) :=
      hyunit.map Algebra.TensorProduct.includeRight.toRingHom
    convert hu using 1
    change m (E (1 - d)) = (1 : R ⧸ I) ⊗ₜ[R] h.hom y
    rw [← hy]
    simp [m]
  have hkdzero : k d = 0 := by
    apply hcompunit.mul_left_cancel
    change k (1 - d) * k d = k (1 - d) * 0
    calc
      k (1 - d) * k d = k ((1 - d) * d) := (map_mul k _ _).symm
      _ = 0 := by rw [hd.one_sub_mul_self, map_zero]
      _ = k (1 - d) * 0 := (mul_zero (k (1 - d))).symm
  have hkst : k.comp s.hom = k.comp t.hom := by
    ext x
    have hxJ : (1 : X) ⊗ₜ[R ⧸ I] x - x ⊗ₜ[R ⧸ I] (1 : X) ∈ J :=
      KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R ⧸ I) x
    rw [hspan, Ideal.mem_span_singleton'] at hxJ
    obtain ⟨a, ha⟩ := hxJ
    have hx := congrArg k (congrArg p ha)
    simp only [map_sub, p, Algebra.TensorProduct.productMap_apply_tmul] at hx
    have hpezero : k (p e) = 0 := by
      change k d = 0
      exact hkdzero
    simp only [map_mul, map_one, one_mul, mul_one] at hx
    rw [hpezero] at hx
    have hxzero : k (p a) * (0 : TensorProduct R (R ⧸ I) Y') = 0 :=
      mul_zero (k (p a))
    have hx' : 0 = k (t.hom x) - k (s.hom x) := by
      exact hxzero ▸ hx
    exact (sub_eq_zero.mp hx'.symm).symm
  refine ⟨Y', h, ?_⟩
  apply Hom.ext
  ext x
  change (baseChangeMap (S := R ⧸ I) h).hom (s.hom x) =
    (baseChangeMap (S := R ⧸ I) h).hom (t.hom x)
  apply (ofEtaleAlgebraEquiv
    (TensorProduct R (R ⧸ I) Y')
      (baseChangePoint (R := R) (S := R ⧸ I) Y')).injective
  rw [ofEtaleAlgebraEquiv_baseChangeMap_apply,
    ofEtaleAlgebraEquiv_baseChangeMap_apply]
  exact DFunLike.congr_fun hkst x

/-- Quotient base change is final on pointed etale neighbourhoods.  The object clause is the
standard-etale lifting theorem, and the morphism clause is the diagonal-idempotent equalization
proved above. -/
theorem quotientBaseChange_final (I : Ideal R) (φ : R ⧸ I →ₐ[R] Ω) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    let _ : IsScalarTower R (R ⧸ I) Ω :=
      IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
    (quotientBaseChange I φ).Final := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  apply Functor.final_of_exists_of_isFiltered
  · exact exists_quotientBaseChange_refinement I φ
  · intro X Y s t
    exact exists_quotientBaseChange_equalizing_refinement I φ s t

end Pcf.Stacks.PointedEtaleNeighborhood
