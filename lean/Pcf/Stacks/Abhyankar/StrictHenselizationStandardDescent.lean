/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.EtaleDescentIsomorphism
public import Pcf.Stacks.Abhyankar.StandardCoverBaseChange
public import Pcf.Stacks.Abhyankar.StrictHenselizationColimit
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Descending strict-local standard covers

This file implements the `05N9` descent paragraph of Stacks Tag `0EYG` for the concrete
pointed-etale colimit used in this repository.  The first step moves a finite family of units
from the strict local colimit to one pointed etale stage, including the inverse identities; the
second descends an isomorphism with a standard tame cover.  The assembled descent paragraph is
`exists_pointedEtale_standardTameCover_of_strict` (`StrictStandardConclusion.lean`).
-/

@[expose] public section

open CategoryTheory Limits
open TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

set_option linter.style.haveILetI false

/-- A finite family of units in the strict local colimit comes from units at one pointed etale
stage.  The inverse identities are descended along the filtered diagram, rather than assumed at
the chosen stage. -/
theorem exists_stage_units (i : Type) [Finite i]
    (unit : i → (LocalColimit R Ω)ˣ) :
    ∃ X : PointedEtaleNeighborhood R Ω, ∃ unitX : i → Xˣ,
      ∀ j, Units.map (toLocalColimitAlgHom (R := R) (Ω := Ω) X) (unitX j) = unit j := by
  classical
  letI := Fintype.ofFinite i
  let s : Set (LocalColimit R Ω) :=
    Set.range (fun p : i × Bool ↦ if p.2 then (unit p.1 : LocalColimit R Ω)
      else (((unit p.1)⁻¹ : (LocalColimit R Ω)ˣ) : LocalColimit R Ω))
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set
    (R := R) (Ω := Ω) s (Set.finite_range _)
  choose x hx using fun j : i ↦ hX (show (unit j : LocalColimit R Ω) ∈ s by
    exact ⟨(j, true), by simp⟩)
  choose y hy using fun j : i ↦ hX
    (show (((unit j)⁻¹ : (LocalColimit R Ω)ˣ) : LocalColimit R Ω) ∈ s by
      exact ⟨(j, false), by simp⟩)
  let F := functor (R := R) (Ω := Ω)
  let G := F ⋙ Under.forget (CommRingCat.of R)
  let c := (Under.forget (CommRingCat.of R)).mapCocone
    (localCocone (R := R) (Ω := Ω))
  have hc : IsColimit c :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R))
      (localCoconeIsColimit (R := R) (Ω := Ω))
  have hxy (j : i) :
      (c.ι.app X).hom (x j * y j) = (c.ι.app X).hom 1 := by
    change toLocalColimitAlgHom (R := R) (Ω := Ω) X (x j * y j) =
      toLocalColimitAlgHom (R := R) (Ω := Ω) X 1
    rw [map_mul, hx j, hy j]
    rw [map_one]
    change (unit j).val * (unit j).inv = 1
    exact Units.val_inv (unit j)
  choose Y f hunit using fun j : i ↦ (hc.eq_iff' (x j * y j) 1).mp (hxy j)
  have hunit' (j : i) : (f j).hom (x j * y j) = (f j).hom 1 := by
    exact hunit j
  obtain ⟨Z, hZ⟩ := IsFiltered.sup_objs_exists (Finset.univ.image Y)
  have hY (j : i) : Y j ∈ Finset.univ.image Y :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let g (j : i) : Y j ⟶ Z := (hZ (hY j)).some
  let fg (j : i) : X ⟶ Z := f j ≫ g j
  let unitZ (j : i) : Zˣ :=
    { val := (fg j).hom (x j)
      inv := (fg j).hom (y j)
      val_inv := by
        change (g j).hom ((f j).hom (x j)) * (g j).hom ((f j).hom (y j)) = 1
        rw [← map_mul, ← map_mul]
        simpa only [map_one] using congrArg (g j).hom (hunit' j)
      inv_val := by
        rw [mul_comm]
        change (g j).hom ((f j).hom (x j)) * (g j).hom ((f j).hom (y j)) = 1
        rw [← map_mul, ← map_mul]
        simpa only [map_one] using congrArg (g j).hom (hunit' j) }
  refine ⟨Z, unitZ, fun j ↦ ?_⟩
  apply Units.ext
  change toLocalColimitAlgHom (R := R) (Ω := Ω) Z ((fg j).hom (x j)) = unit j
  calc
    toLocalColimitAlgHom (R := R) (Ω := Ω) Z ((fg j).hom (x j)) =
        toLocalColimitAlgHom (R := R) (Ω := Ω) X (x j) :=
      DFunLike.congr_fun
        (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) (fg j)) (x j)
    _ = unit j := hx j

#print axioms exists_stage_units

end Pcf.Stacks.PointedEtaleNeighborhood

namespace Pcf.Stacks.EtaleDescent.StageAlgebra.EquivalenceDescent

variable {J : Type u} [SmallCategory J]
variable (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc

/-- A standard-cover algebra at one stage that becomes equivalent to a second finitely
presented algebra over the limit is standard after passage to one later stage.  This is the
exact output form of the coherent `05N9` isomorphism descent needed by Tag `0EYG`. -/
theorem exists_stage_standardTameCover_of_limit_equiv
    (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B] [IsNoetherianRing (F.obj i)]
    [IsFiltered J] {a : F.obj i}
    (hA : IsFiniteDisjointUnionOfStandardTameCovers (F.obj i) A a)
    (hB : Algebra.FinitePresentation (F.obj i) B)
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) :
    ∃ X : Under i,
      IsFiniteDisjointUnionOfStandardTameCovers
        (StageRing F i X) (StageBaseChange F i B X)
        (algebraMap (F.obj i) (StageRing F i X) a) := by
  obtain ⟨P⟩ := exists_descendedAlgEquiv_of_standardTameCover F c hc i A B hA hB e
  refine ⟨P.stage, ?_⟩
  rcases hA.baseChange (T := StageRing F i P.stage) with
    ⟨ι, hι, exponent, unit, hexponent, hexponentUnit, ⟨hstandard⟩⟩
  let commStage : StageBaseChange F i A P.stage ≃ₐ[StageRing F i P.stage]
      TensorProduct (F.obj i) (StageRing F i P.stage) A :=
    { Algebra.TensorProduct.comm (F.obj i) A (StageRing F i P.stage) with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm (F.obj i) A (StageRing F i P.stage)
          (1 ⊗ₜ[(F.obj i)] r) = r ⊗ₜ[(F.obj i)] 1
        rfl }
  exact ⟨ι, hι, exponent, unit, hexponent, hexponentUnit,
    ⟨P.equiv.symm.trans (commStage.trans hstandard)⟩⟩

#print axioms exists_stage_standardTameCover_of_limit_equiv

end Pcf.Stacks.EtaleDescent.StageAlgebra.EquivalenceDescent
