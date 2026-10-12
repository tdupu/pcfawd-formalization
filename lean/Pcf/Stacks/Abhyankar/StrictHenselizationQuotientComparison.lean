/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.StrictHenselizationLocalBaseChange
import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientFinality

/-!
# Quotient comparison for the pointed-etale colimit

Finality of quotient base change lets the target colimit detect equality already after a
refinement indexed by an original pointed etale neighbourhood.  Combined with the stagewise
quotient/base-change equivalence, this proves that the canonical quotient comparison on the
unlocalized colimits is bijective.
-/

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Equality in the quotient pointed-etale colimit is detected after a refinement that is itself
the base change of a pointed-etale neighbourhood over the original ring. -/
theorem exists_baseChange_refinement_of_toColimit_eq (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    let _ : IsScalarTower R (R ⧸ I) Ω :=
      IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
    ∀ {Y : PointedEtaleNeighborhood R Ω}
      {x y : baseChangeObj (R := R) (S := R ⧸ I) Y},
      toColimit (R := R ⧸ I) (Ω := Ω)
          (baseChangeObj (R := R) (S := R ⧸ I) Y) x =
        toColimit (R := R ⧸ I) (Ω := Ω)
          (baseChangeObj (R := R) (S := R ⧸ I) Y) y →
      ∃ (Y' : PointedEtaleNeighborhood R Ω) (f : Y ⟶ Y'),
        (baseChangeMap (S := R ⧸ I) f).hom x =
          (baseChangeMap (S := R ⧸ I) f).hom y := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  change ∀ {Y : PointedEtaleNeighborhood R Ω}
    {x y : baseChangeObj (R := R) (S := R ⧸ I) Y},
    toColimit (R := R ⧸ I) (Ω := Ω)
        (baseChangeObj (R := R) (S := R ⧸ I) Y) x =
      toColimit (R := R ⧸ I) (Ω := Ω)
        (baseChangeObj (R := R) (S := R ⧸ I) Y) y →
    ∃ (Y' : PointedEtaleNeighborhood R Ω) (f : Y ⟶ Y'),
      (baseChangeMap (S := R ⧸ I) f).hom x =
        (baseChangeMap (S := R ⧸ I) f).hom y
  intro Y x y hxy
  let F := quotientBaseChange I φ
  let G := functor (R := R ⧸ I) (Ω := Ω)
  let U := Under.forget (CommRingCat.of (R ⧸ I))
  let V := forget CommRingCat
  let c := V.mapCocone (U.mapCocone (colimit.cocone G))
  have hcTarget : IsColimit c :=
    isColimitOfPreserves V (isColimitOfPreserves U (colimit.isColimit G))
  let _ : F.Final := quotientBaseChange_final I φ
  have hc : IsColimit (c.whisker F) :=
    (Functor.Final.isColimitWhiskerEquiv F c).symm hcTarget
  have hxy' : (c.whisker F).ι.app Y x = (c.whisker F).ι.app Y y := by
    exact hxy
  obtain ⟨Y', f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hc x y).mp hxy'
  refine ⟨Y', f, ?_⟩
  exact hf

/-- The quotient comparison on the unlocalized pointed-etale colimits is surjective. -/
theorem colimitQuotientBaseChangeAlgHom_surjective (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    Function.Surjective (colimitQuotientBaseChangeAlgHom I φ) := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  change Function.Surjective (colimitQuotientBaseChangeAlgHom I φ)
  intro z
  obtain ⟨X, x, hx⟩ :=
    exists_stage_of_colimit_element (R := R ⧸ I) (Ω := Ω) z
  obtain ⟨Y, ⟨s⟩⟩ := exists_quotientBaseChange_refinement I φ X
  change X ⟶ baseChangeObj (R := R) (S := R ⧸ I) Y at s
  let E : baseChangeObj (R := R) (S := R ⧸ I) Y ≃ₐ[R ⧸ I]
      TensorProduct R (R ⧸ I) Y :=
    ofEtaleAlgebraEquiv (TensorProduct R (R ⧸ I) Y)
      (baseChangePoint (R := R) (S := R ⧸ I) Y)
  obtain ⟨y, hy⟩ : ∃ y : Y, (1 : R ⧸ I) ⊗ₜ[R] y = E (s.hom x) := by
    obtain ⟨q, hq⟩ := (quotientStageEquiv I Y).surjective (E (s.hom x))
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨y, (quotientStageEquiv_mk I Y y).trans hq⟩
  refine ⟨Ideal.Quotient.mk _
    (toColimit (R := R) (Ω := Ω) Y y), ?_⟩
  rw [colimitQuotientBaseChangeAlgHom_mk]
  change colimitBaseChangeRingHom (R := R) (S := R ⧸ I) (Ω := Ω)
      (toColimit (R := R) (Ω := Ω) Y y) = z
  rw [colimitBaseChangeRingHom_toColimit]
  change toColimit (R := R ⧸ I) (Ω := Ω)
      (baseChangeObj (R := R) (S := R ⧸ I) Y)
        (E.symm ((1 : R ⧸ I) ⊗ₜ[R] y)) = z
  rw [hy, E.symm_apply_apply]
  exact (DFunLike.congr_fun
    (toColimit_naturality (R := R ⧸ I) (Ω := Ω) s) x).trans hx

/-- The quotient comparison on the unlocalized pointed-etale colimits is injective. -/
theorem colimitQuotientBaseChangeAlgHom_injective (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    Function.Injective (colimitQuotientBaseChangeAlgHom I φ) := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  change Function.Injective (colimitQuotientBaseChangeAlgHom I φ)
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨Y, y, hyc⟩ := exists_stage_of_colimit_element (R := R) (Ω := Ω) c
  change quotientColimitBaseChangeRingHom I φ c = 0 at hq
  rw [← hyc] at hq
  change colimitBaseChangeRingHom (R := R) (S := R ⧸ I) (Ω := Ω)
      (toColimit (R := R) (Ω := Ω) Y y) = 0 at hq
  rw [colimitBaseChangeRingHom_toColimit] at hq
  let E : baseChangeObj (R := R) (S := R ⧸ I) Y ≃ₐ[R ⧸ I]
      TensorProduct R (R ⧸ I) Y :=
    ofEtaleAlgebraEquiv (TensorProduct R (R ⧸ I) Y)
      (baseChangePoint (R := R) (S := R ⧸ I) Y)
  let z : baseChangeObj (R := R) (S := R ⧸ I) Y :=
    E.symm ((1 : R ⧸ I) ⊗ₜ[R] y)
  have hz : toColimit (R := R ⧸ I) (Ω := Ω)
      (baseChangeObj (R := R) (S := R ⧸ I) Y) z =
        toColimit (R := R ⧸ I) (Ω := Ω)
          (baseChangeObj (R := R) (S := R ⧸ I) Y) 0 := by
    change stageToBaseChangeColimit (S := R ⧸ I) Y y =
      toColimit (R := R ⧸ I) (Ω := Ω)
        (baseChangeObj (R := R) (S := R ⧸ I) Y) 0
    rw [map_zero]
    exact hq
  obtain ⟨Y', f, hf⟩ :=
    exists_baseChange_refinement_of_toColimit_eq I φ hz
  have htensor : (1 : R ⧸ I) ⊗ₜ[R] f.hom y =
      (0 : TensorProduct R (R ⧸ I) Y') := by
    let E' : baseChangeObj (R := R) (S := R ⧸ I) Y' ≃ₐ[R ⧸ I]
        TensorProduct R (R ⧸ I) Y' :=
      ofEtaleAlgebraEquiv (TensorProduct R (R ⧸ I) Y')
        (baseChangePoint (R := R) (S := R ⧸ I) Y')
    have hE := congrArg E' hf
    change E' ((baseChangeMap (S := R ⧸ I) f).hom z) =
      E' ((baseChangeMap (S := R ⧸ I) f).hom 0) at hE
    rw [ofEtaleAlgebraEquiv_baseChangeMap_apply, map_zero, map_zero] at hE
    change baseChangeRawMap (S := R ⧸ I) f
      (E (E.symm ((1 : R ⧸ I) ⊗ₜ[R] y))) = 0 at hE
    rw [E.apply_symm_apply] at hE
    simpa [baseChangeRawMap] using hE
  have hquot : Ideal.Quotient.mk (I.map (algebraMap R Y')) (f.hom y) = 0 := by
    apply (quotientStageEquiv I Y').injective
    rw [quotientStageEquiv_mk, map_zero]
    exact htensor
  have hmemY' : f.hom y ∈ I.map (algebraMap R Y') :=
    Ideal.Quotient.eq_zero_iff_mem.mp hquot
  have hmemC' : toColimit (R := R) (Ω := Ω) Y' (f.hom y) ∈
      I.map (algebraMap R (Colimit R Ω)) := by
    have hmap := Ideal.mem_map_of_mem
      (toColimit (R := R) (Ω := Ω) Y').toRingHom hmemY'
    have hcomp : (toColimit (R := R) (Ω := Ω) Y').toRingHom.comp
        (algebraMap R Y') = algebraMap R (Colimit R Ω) := by
      ext r
      exact (toColimit (R := R) (Ω := Ω) Y').commutes r
    rw [Ideal.map_map, hcomp] at hmap
    exact hmap
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hyc]
  rw [← DFunLike.congr_fun (toColimit_naturality (R := R) (Ω := Ω) f) y]
  exact hmemC'

/-- The quotient comparison on the unlocalized pointed-etale colimits is bijective. -/
theorem colimitQuotientBaseChangeAlgHom_bijective (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    Function.Bijective (colimitQuotientBaseChangeAlgHom I φ) :=
  ⟨colimitQuotientBaseChangeAlgHom_injective I φ,
    colimitQuotientBaseChangeAlgHom_surjective I φ⟩

end Pcf.Stacks.PointedEtaleNeighborhood
