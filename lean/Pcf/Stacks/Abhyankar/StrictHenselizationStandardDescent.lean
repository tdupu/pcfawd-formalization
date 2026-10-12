/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.EtaleDescentIsomorphism
import Pcf.Stacks.Abhyankar.StandardCoverBaseChange
import Pcf.Stacks.Abhyankar.StrictHenselizationColimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Descending strict-local standard covers

This file implements the `05N9` descent paragraph of Stacks Tag `0EYG` for the concrete
pointed-etale colimit used in this repository.  The first step moves a finite family of units
from the strict local colimit to one pointed etale stage, including the inverse identities.
-/

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

namespace Pcf.Stacks.PointedEtaleNeighborhood

open Pcf.Stacks.EtaleDescent
open Pcf.Stacks.EtaleDescent.StageAlgebra
open Pcf.Stacks.EtaleDescent.StageAlgebra.EquivalenceDescent

set_option linter.style.haveILetI false

/-- The complete descent paragraph of Stacks Tag `0EYG`: a standard-cover presentation after
passage to the strict local colimit descends to one actual pointed etale neighbourhood.  All
coefficients and both inverse identities of the algebra equivalence are descended; the only
input not produced here is the strict-local standard presentation itself. -/
theorem exists_pointedEtale_standardTameCover_of_strict
    {R Ω S : Type u} [CommRing R] [Field Ω] [CommRing S]
    [Algebra R Ω] [Algebra R S] [IsNoetherianRing R]
    (a : R) [Module.Finite R S]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (hstrict : IsFiniteDisjointUnionOfStandardTameCovers
      (LocalColimit R Ω) (TensorProduct R (LocalColimit R Ω) S)
      (algebraMap R (LocalColimit R Ω) a)) :
    ∃ X : PointedEtaleNeighborhood R Ω,
      IsFiniteDisjointUnionOfStandardTameCovers X
        (X ⊗[R] S) (algebraMap R X a) := by
  classical
  let L := LocalColimit R Ω
  rcases hstrict with
    ⟨ι, hι, exponent, unit, hexponent, _hexponentUnit, ⟨hstrictEquiv⟩⟩
  letI := hι
  obtain ⟨X, unitX, hunitX⟩ := exists_stage_units ι unit
  let F := functor (R := R) (Ω := Ω)
  let c := localCocone (R := R) (Ω := Ω)
  let G := F ⋙ Under.forget (CommRingCat.of R)
  let d := (Under.forget (CommRingCat.of R)).mapCocone c
  have hd : IsColimit d :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R))
      (localCoconeIsColimit (R := R) (Ω := Ω))
  let _ : Algebra X L := (c.ι.app X).right.hom.toAlgebra
  let _ : IsScalarTower R X L :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := X) (A := L) (fun r ↦ by
      change algebraMap R L r = (c.ι.app X).right.hom (algebraMap R X r)
      exact (congr($((c.ι.app X).w).hom r)).symm)
  let A := ∀ j, AdjoinRoot
    (Pcf.LocalModel.localPoly (unitX j) (algebraMap R X a) (exponent j))
  let B := X ⊗[R] S
  letI : CommRing B := by dsimp [B]; infer_instance
  letI : Algebra X B := Algebra.TensorProduct.leftAlgebra
  letI : Algebra (G.obj X) A := by
    change Algebra X A
    infer_instance
  letI : Algebra (G.obj X) B := by
    change Algebra X B
    infer_instance
  letI : IsNoetherianRing (G.obj X) := by
    change IsNoetherianRing X
    infer_instance
  have hA : IsFiniteDisjointUnionOfStandardTameCovers X A (algebraMap R X a) := by
    refine ⟨ι, inferInstance, exponent, unitX, hexponent, ?_, ⟨AlgEquiv.refl⟩⟩
    intro j
    simpa using (hnat (exponent j) (hexponent j)).map (algebraMap R X)
  letI : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.FinitePresentation X B := Algebra.FinitePresentation.baseChange X
  letI : Algebra.FinitePresentation (G.obj X) B := by
    change Algebra.FinitePresentation X B
    infer_instance
  letI : Algebra L (A ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (B ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  have hunitXL (j : ι) : Units.map (algebraMap X L) (unitX j) = unit j := by
    exact hunitX j
  let commA : A ⊗[X] L ≃ₐ[L] L ⊗[X] A :=
    { Algebra.TensorProduct.comm X A L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X A L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let standardBaseChange : L ⊗[X] A ≃ₐ[L]
      ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j)
        (algebraMap R L a) (exponent j)) := by
    let e₁ := standardCoversBaseChangeEquivOfUnitEq ι unitX unit hunitXL
      (algebraMap R X a) exponent
    let e₂ : (∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j)
        (algebraMap X L (algebraMap R X a)) (exponent j))) ≃ₐ[L]
        ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j)
          (algebraMap R L a) (exponent j)) :=
      AlgEquiv.piCongrRight (fun j ↦ AdjoinRoot.algEquivOfEq L _ _ (by
        rw [IsScalarTower.algebraMap_apply R X L]))
    exact e₁.trans e₂
  let commB : B ⊗[X] L ≃ₐ[L] L ⊗[X] B :=
    { Algebra.TensorProduct.comm X B L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X B L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelB : L ⊗[X] B ≃ₐ[L] L ⊗[R] S :=
    Algebra.TensorProduct.cancelBaseChange R X L L S
  let limitEquiv : A ⊗[X] L ≃ₐ[L] B ⊗[X] L :=
    (commA.trans standardBaseChange).trans
      ((commB.trans cancelB).trans hstrictEquiv).symm
  let limitEquiv' : LimitBaseChange G d X A ≃ₐ[LimitRing G d X]
      LimitBaseChange G d X B := by
    change A ⊗[X] L ≃ₐ[L] B ⊗[X] L
    exact limitEquiv
  obtain ⟨Y, hY⟩ := exists_stage_standardTameCover_of_limit_equiv
    (F := G) (c := d) (hc := hd)
    (i := X) (A := A) (B := B) (a := algebraMap R X a)
    hA inferInstance limitEquiv'
  rcases hY with ⟨κ, hκ, d, v, hd, hdUnit, ⟨hYEquiv⟩⟩
  let T := StageRing G X Y
  letI : Algebra X T := by
    change Algebra (G.obj X) T
    infer_instance
  letI : Algebra R T := by
    change Algebra R Y.right
    infer_instance
  letI : IsScalarTower R X T :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := X) (A := T) (fun r ↦ by
      change algebraMap R Y.right r = Y.hom.hom (algebraMap R X r)
      exact (Y.hom.hom.commutes r).symm)
  let commStage : StageBaseChange G X B Y ≃ₐ[T] T ⊗[X] B :=
    { Algebra.TensorProduct.comm X B T with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X B T (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelStage : T ⊗[X] B ≃ₐ[T] T ⊗[R] S :=
    Algebra.TensorProduct.cancelBaseChange R X T T S
  let hYEquiv' : StageBaseChange G X B Y ≃ₐ[T]
      ∀ j, AdjoinRoot
        (Pcf.LocalModel.localPoly (v j) (algebraMap R T a) (d j)) :=
    hYEquiv.trans (AlgEquiv.piCongrRight (fun j ↦ AdjoinRoot.algEquivOfEq T _ _ (by
      change Pcf.LocalModel.localPoly (v j)
        (algebraMap X T (algebraMap R X a)) (d j) =
        Pcf.LocalModel.localPoly (v j) (algebraMap R T a) (d j)
      rw [IsScalarTower.algebraMap_apply R X T])))
  refine ⟨Y.right, κ, hκ, d, v, hd, hdUnit, ?_⟩
  change Nonempty (T ⊗[R] S ≃ₐ[T] ∀ j, AdjoinRoot
    (Pcf.LocalModel.localPoly (v j) (algebraMap R T a) (d j)))
  exact ⟨(commStage.trans cancelStage).symm.trans hYEquiv'⟩

#print axioms exists_pointedEtale_standardTameCover_of_strict

end Pcf.Stacks.PointedEtaleNeighborhood
