/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Pcf.Stacks.Abhyankar.EtaleDescentObjects
public import Pcf.Stacks.Abhyankar.StrictHenselizationConstruction

/-!
# Moving finite data to a pointed etale stage

Every finite set in the filtered colimit comes from one pointed etale stage.  The analogous
statement for its localization at the geometric point also holds: represent each element by a
fraction, move its numerator and denominator to a stage, and localize that stage away from the
denominator.  A final filtered common refinement puts finitely many such elements at one stage.

These lemmas are the concrete bridge from finite-presentation descent to the local candidate for
the strict henselization.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Every element of the filtered colimit comes from a pointed etale stage. -/
theorem exists_stage_of_colimit_element (c : Colimit R Ω) :
    ∃ (X : PointedEtaleNeighborhood R Ω) (x : X),
      toColimit (R := R) (Ω := Ω) X x = c := by
  let F := functor (R := R) (Ω := Ω)
  have hU := isColimitOfPreserves (Under.forget (CommRingCat.of R)) (colimit.isColimit F)
  have hR := isColimitOfPreserves (forget CommRingCat) hU
  obtain ⟨X, x, hx⟩ := Types.jointly_surjective_of_isColimit hR c
  exact ⟨X, x, hx⟩

/-- Every finite set in the filtered colimit comes from one pointed etale stage. -/
theorem exists_stage_containing_finite_colimit_set
    (s : Set (Colimit R Ω)) (hs : s.Finite) :
    ∃ X : PointedEtaleNeighborhood R Ω,
      s ⊆ Set.range (toColimit (R := R) (Ω := Ω) X) := by
  let F := functor (R := R) (Ω := Ω)
  let G := F ⋙ Under.forget (CommRingCat.of R)
  let c := (Under.forget (CommRingCat.of R)).mapCocone (colimit.cocone F)
  have hc : IsColimit c :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R)) (colimit.isColimit F)
  obtain ⟨X, hX⟩ := Pcf.Stacks.EtaleDescent.exists_stage_containing_finite_set G c hc s hs
  refine ⟨X, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hX hx
  exact ⟨y, hy⟩

/-- The canonical algebra map from a pointed etale stage to the localized filtered colimit. -/
noncomputable def toLocalColimitAlgHom (X : PointedEtaleNeighborhood R Ω) :
    X →ₐ[R] LocalColimit R Ω :=
  (IsScalarTower.toAlgHom R (Colimit R Ω) (LocalColimit R Ω)).comp
    (toColimit (R := R) (Ω := Ω) X)

/-- The maps from pointed stages to the filtered colimit form a cocone. -/
theorem toColimit_naturality {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (toColimit (R := R) (Ω := Ω) Y).comp f.hom =
      toColimit (R := R) (Ω := Ω) X := by
  ext x
  exact congr($(colimit.w (functor (R := R) (Ω := Ω)) f).right.hom x)

/-- The maps from pointed stages to the localized filtered colimit are natural. -/
theorem toLocalColimitAlgHom_naturality
    {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (toLocalColimitAlgHom (R := R) (Ω := Ω) Y).comp f.hom =
      toLocalColimitAlgHom X := by
  ext x
  change algebraMap (Colimit R Ω) (LocalColimit R Ω)
    (toColimit (R := R) (Ω := Ω) Y (f.hom x)) =
    algebraMap (Colimit R Ω) (LocalColimit R Ω)
      (toColimit (R := R) (Ω := Ω) X x)
  exact congrArg (algebraMap (Colimit R Ω) (LocalColimit R Ω))
    (DFunLike.congr_fun (toColimit_naturality (R := R) (Ω := Ω) f) x)

/-- Every element of the localized filtered colimit comes from a pointed etale stage. -/
theorem exists_stage_of_localColimit_element (a : LocalColimit R Ω) :
    ∃ (X : PointedEtaleNeighborhood R Ω) (x : X),
      toLocalColimitAlgHom X x = a := by
  let C := Colimit R Ω
  let I := colimitPointPrime (R := R) (Ω := Ω)
  obtain ⟨c, d, hcd⟩ := IsLocalization.exists_mk'_eq I.primeCompl a
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_colimit_set
    (R := R) (Ω := Ω) ({c, (d : C)} : Set C) (Set.toFinite {c, (d : C)})
  have hc : c ∈ ({c, (d : C)} : Set C) := by simp
  have hd : (d : C) ∈ ({c, (d : C)} : Set C) := by simp
  obtain ⟨x, hx⟩ := hX hc
  obtain ⟨y, hy⟩ := hX hd
  have hpointy : X.point y ≠ 0 := by
    intro hzero
    have hcy : colimitPoint (R := R) (Ω := Ω) (d : C) = 0 := by
      rw [← hy]
      exact (DFunLike.congr_fun
        (colimitPoint_comp_toColimit (R := R) (Ω := Ω) X) y).trans hzero
    exact (Ideal.mem_primeCompl_iff.mp d.property) hcy
  have hpointyUnit : IsUnit (X.point y) := isUnit_iff_ne_zero.mpr hpointy
  let L := Localization.Away y
  let pointL : L →ₐ[R] Ω := IsLocalization.Away.liftAlgHom y (f := X.point) hpointyUnit
  let N := ofEtaleAlgebra L pointL
  let j : X ⟶ N := homToOfEtaleAlgebra L pointL
    (IsScalarTower.toAlgHom R X L) (by
      ext z
      simp [pointL])
  let den : Submonoid.powers y := ⟨y, ⟨1, by simp⟩⟩
  let l : L := IsLocalization.mk' L x den
  let n : N := (ofEtaleAlgebraEquiv L pointL).symm l
  refine ⟨N, n, ?_⟩
  rw [← hcd]
  apply (IsLocalization.eq_mk'_iff_mul_eq (M := I.primeCompl)).mpr
  change toLocalColimitAlgHom N n * algebraMap C (LocalColimit R Ω) (d : C) =
    algebraMap C (LocalColimit R Ω) c
  rw [← hy, ← hx]
  change toLocalColimitAlgHom N n * toLocalColimitAlgHom X y =
    toLocalColimitAlgHom X x
  rw [← DFunLike.congr_fun
      (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) j) y,
    ← DFunLike.congr_fun
      (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) j) x]
  change toLocalColimitAlgHom N n * toLocalColimitAlgHom N (j.hom y) =
    toLocalColimitAlgHom N (j.hom x)
  rw [← map_mul]
  congr 1
  apply (ofEtaleAlgebraEquiv L pointL).injective
  change (ofEtaleAlgebraEquiv L pointL)
    ((ofEtaleAlgebraEquiv L pointL).symm l *
      (ofEtaleAlgebraEquiv L pointL).symm (algebraMap X L y)) =
    (ofEtaleAlgebraEquiv L pointL)
      ((ofEtaleAlgebraEquiv L pointL).symm (algebraMap X L x))
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  exact IsLocalization.mk'_spec L x den

/-- Every finite set in the localized filtered colimit comes from one pointed etale stage. -/
theorem exists_stage_containing_finite_localColimit_set
    (s : Set (LocalColimit R Ω)) (hs : s.Finite) :
    ∃ X : PointedEtaleNeighborhood R Ω,
      s ⊆ Set.range (toLocalColimitAlgHom (R := R) (Ω := Ω) X) := by
  classical
  let _ : Fintype s := hs.fintype
  choose X x hx using fun a : s ↦
    exists_stage_of_localColimit_element (R := R) (Ω := Ω) a.1
  obtain ⟨Y, hY⟩ := IsFiltered.sup_objs_exists (Finset.univ.image X)
  have hX (a : s) : X a ∈ Finset.univ.image X :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  let f (a : s) : X a ⟶ Y := (hY (hX a)).some
  refine ⟨Y, fun a ha ↦ ?_⟩
  let a' : s := ⟨a, ha⟩
  refine ⟨(f a').hom (x a'), ?_⟩
  exact (DFunLike.congr_fun
    (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) (f a')) (x a')).trans (hx a')

end Pcf.Stacks.PointedEtaleNeighborhood
