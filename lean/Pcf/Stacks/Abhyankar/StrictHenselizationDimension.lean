/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Pcf.Stacks.Abhyankar.StrictHenselizationBase

/-!
# Dimension of the strict local colimit

This file develops the flatness and dimension comparison needed for Stacks Tag `06LN`.
Finite relations in the localized filtered colimit already vanish at a pointed etale stage;
the equational criterion therefore makes the strict local colimit flat over its base.
-/

open CategoryTheory Limits

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- If an element of a pointed etale stage vanishes in the strict local colimit, it vanishes
after passage to a further pointed etale stage. -/
theorem exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero
    (X : PointedEtaleNeighborhood R Ω) (x : X)
    (hx : toLocalColimitAlgHom (R := R) (Ω := Ω) X x = 0) :
    ∃ (Y : PointedEtaleNeighborhood R Ω) (f : X ⟶ Y), f.hom x = 0 := by
  let C := Colimit R Ω
  let Q := colimitPointPrime (R := R) (Ω := Ω)
  have hx' : algebraMap C (LocalColimit R Ω)
      (toColimit (R := R) (Ω := Ω) X x) = 0 := by
    exact hx
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff Q.primeCompl (LocalColimit R Ω)
      (toColimit (R := R) (Ω := Ω) X x)).mp hx'
  obtain ⟨Z, z, hz⟩ := exists_stage_of_colimit_element (R := R) (Ω := Ω) (s : C)
  obtain ⟨W, ⟨fX⟩, ⟨fZ⟩⟩ := exists_common_refinement (R := R) (Ω := Ω) X Z
  have hprod : toColimit (R := R) (Ω := Ω) W (fZ.hom z * fX.hom x) = 0 := by
    calc
      toColimit (R := R) (Ω := Ω) W (fZ.hom z * fX.hom x) =
          toColimit (R := R) (Ω := Ω) Z z *
            toColimit (R := R) (Ω := Ω) X x := by
        rw [map_mul]
        congr 1
        · exact DFunLike.congr_fun
            (toColimit_naturality (R := R) (Ω := Ω) fZ) z
        · exact DFunLike.congr_fun
            (toColimit_naturality (R := R) (Ω := Ω) fX) x
      _ = (s : C) * toColimit (R := R) (Ω := Ω) X x := by rw [hz]
      _ = 0 := hs
  let F := functor (R := R) (Ω := Ω)
  let G := F ⋙ Under.forget (CommRingCat.of R)
  let c := (Under.forget (CommRingCat.of R)).mapCocone (colimit.cocone F)
  have hc : IsColimit c :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R)) (colimit.isColimit F)
  obtain ⟨V, hWV, hzero⟩ :=
    (hc.eq_iff' (fZ.hom z * fX.hom x) (0 : W)).mp (by
        change toColimit (R := R) (Ω := Ω) W (fZ.hom z * fX.hom x) =
          toColimit (R := R) (Ω := Ω) W 0
        simpa using hprod)
  have hpointz0 : Z.point z ≠ 0 := by
    intro h
    apply (Ideal.mem_primeCompl_iff.mp s.property)
    rw [← hz]
    exact (DFunLike.congr_fun
      (colimitPoint_comp_toColimit (R := R) (Ω := Ω) Z) z).trans h
  have hpointz : V.point (hWV.hom (fZ.hom z)) ≠ 0 := by
    change (V.point.comp hWV.hom) (fZ.hom z) ≠ 0
    rw [hWV.point_comp]
    change (W.point.comp fZ.hom) z ≠ 0
    rw [fZ.point_comp]
    exact hpointz0
  have hpointzUnit : IsUnit (V.point (hWV.hom (fZ.hom z))) :=
    isUnit_iff_ne_zero.mpr hpointz
  let L := Localization.Away (hWV.hom (fZ.hom z))
  let pointL : L →ₐ[R] Ω :=
    IsLocalization.Away.liftAlgHom (hWV.hom (fZ.hom z))
      (f := V.point) hpointzUnit
  let Y := ofEtaleAlgebra L pointL
  let hVY : V ⟶ Y := homToOfEtaleAlgebra L pointL
    (IsScalarTower.toAlgHom R V L) (by
      ext v
      simp [pointL])
  let f : X ⟶ Y := fX ≫ hWV ≫ hVY
  refine ⟨Y, f, ?_⟩
  have hzero' : hWV.hom (fZ.hom z) * hWV.hom (fX.hom x) = 0 := by
    change hWV.hom (fZ.hom z * fX.hom x) = hWV.hom 0 at hzero
    simpa only [map_mul, map_zero] using hzero
  have hzeroL := congrArg (algebraMap V L) hzero'
  change (ofEtaleAlgebraEquiv L pointL).symm
    (algebraMap V L (hWV.hom (fX.hom x))) = 0
  apply (ofEtaleAlgebraEquiv L pointL).injective
  simp only [AlgEquiv.apply_symm_apply, map_zero]
  apply (IsLocalization.Away.algebraMap_isUnit
    (hWV.hom (fZ.hom z)) (S := L)).mul_left_cancel
  simpa only [map_mul, map_zero, mul_zero] using hzeroL

/-- The canonical map from the base to the strict local colimit is flat. -/
theorem localColimit_flat : Module.Flat R (LocalColimit R Ω) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hx
  classical
  let s : Set (LocalColimit R Ω) := Set.range x
  have hs : s.Finite := Set.finite_range x
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set
    (R := R) (Ω := Ω) s hs
  choose xX hxX using fun i : Fin l ↦ hX (Set.mem_range_self i)
  let z : X := ∑ i, f i • xX i
  have hz : toLocalColimitAlgHom (R := R) (Ω := Ω) X z = 0 := by
    rw [map_sum]
    simpa only [z, map_smul, hxX] using hx
  obtain ⟨Y, g, hg⟩ :=
    exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero
      (R := R) (Ω := Ω) X z hz
  have hrelY : ∑ i, f i • g.hom (xX i) = 0 := by
    simpa only [z, map_sum, map_smul] using hg
  obtain ⟨k, a, y, hxy, hfa⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrelY
  refine ⟨k, a, fun j ↦ toLocalColimitAlgHom (R := R) (Ω := Ω) Y (y j), ?_, hfa⟩
  intro i
  calc
    x i = toLocalColimitAlgHom (R := R) (Ω := Ω) X (xX i) := (hxX i).symm
    _ = toLocalColimitAlgHom (R := R) (Ω := Ω) Y (g.hom (xX i)) :=
      (DFunLike.congr_fun
        (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) g) (xX i)).symm
    _ = toLocalColimitAlgHom (R := R) (Ω := Ω) Y (∑ j, a i j • y j) := by
      exact congrArg (toLocalColimitAlgHom (R := R) (Ω := Ω) Y) (hxy i)
    _ = ∑ j, a i j • toLocalColimitAlgHom (R := R) (Ω := Ω) Y (y j) := by
      rw [map_sum]
      simp only [map_smul]

/-- The canonical map from the base to the strict local colimit is faithfully flat. -/
theorem localColimit_faithfullyFlat [IsLocalRing R]
    [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
    [IsSepClosure (IsLocalRing.ResidueField R) Ω] :
    Module.FaithfullyFlat R (LocalColimit R Ω) := by
  let _ : Module.Flat R (LocalColimit R Ω) := localColimit_flat (R := R) (Ω := Ω)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end Pcf.Stacks.PointedEtaleNeighborhood
