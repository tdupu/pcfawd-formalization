/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationStages

/-!
# The strict local colimit is still the pointed-etale colimit

The strict local model is defined by localizing the filtered colimit of pointed etale
neighbourhoods at its geometric point.  Every element inverted by this localization is already
inverted at a further pointed etale stage.  Consequently the localization map is an equivalence,
and the local model itself is a colimit of the original pointed-etale diagram.

This is the categorical bridge needed to apply Stacks Tag `05N9` directly to a finite
presentation over the strict henselization in the descent paragraph of Tag `0EYG`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Every element inverted in the localization defining the strict local colimit is already a
unit in the unlocalized pointed-etale colimit: invert a representative at one further etale
stage. -/
theorem colimitPointPrime_primeCompl_le_isUnit :
    (colimitPointPrime (R := R) (Ω := Ω)).primeCompl ≤
      IsUnit.submonoid (Colimit R Ω) := by
  intro s hs
  obtain ⟨X, x, hx⟩ :=
    exists_stage_of_colimit_element (R := R) (Ω := Ω) (s : Colimit R Ω)
  have hpointx : X.point x ≠ 0 := by
    intro hzero
    apply (Ideal.mem_primeCompl_iff.mp hs)
    change colimitPoint (R := R) (Ω := Ω) (s : Colimit R Ω) = 0
    rw [← hx]
    exact (DFunLike.congr_fun
      (colimitPoint_comp_toColimit (R := R) (Ω := Ω) X) x).trans hzero
  have hpointxUnit : IsUnit (X.point x) := isUnit_iff_ne_zero.mpr hpointx
  let L := Localization.Away x
  let pointL : L →ₐ[R] Ω := IsLocalization.Away.liftAlgHom x (f := X.point) hpointxUnit
  let N := ofEtaleAlgebra L pointL
  let j : X ⟶ N := homToOfEtaleAlgebra L pointL
    (IsScalarTower.toAlgHom R X L) (by
      ext z
      simp [pointL])
  have hjunit : IsUnit (j.hom x) := by
    change IsUnit ((ofEtaleAlgebraEquiv L pointL).symm (algebraMap X L x))
    exact IsUnit.map (ofEtaleAlgebraEquiv L pointL).symm
      (IsLocalization.Away.algebraMap_isUnit x)
  have hmapunit : IsUnit
      (toColimit (R := R) (Ω := Ω) N (j.hom x)) :=
    hjunit.map (toColimit (R := R) (Ω := Ω) N).toRingHom
  have hjmap : toColimit (R := R) (Ω := Ω) N (j.hom x) =
      toColimit (R := R) (Ω := Ω) X x :=
    DFunLike.congr_fun (toColimit_naturality (R := R) (Ω := Ω) j) x
  rw [hjmap] at hmapunit
  change IsUnit (s : Colimit R Ω)
  rw [← hx]
  exact hmapunit

/-- The localization used to define the strict local colimit does not change the colimit: all
its denominators are already units after passage to pointed etale stages. -/
noncomputable def colimitToLocalColimitAlgEquiv :
    Colimit R Ω ≃ₐ[R] LocalColimit R Ω :=
  (IsLocalization.atUnits (Colimit R Ω)
      (colimitPointPrime (R := R) (Ω := Ω)).primeCompl
      colimitPointPrime_primeCompl_le_isUnit).restrictScalars R

/-- The legs from pointed etale stages to the strict local colimit. -/
noncomputable def localCocone : Cocone (functor (R := R) (Ω := Ω)) where
  pt := CommRingCat.mkUnder (CommRingCat.of R) (LocalColimit R Ω)
  ι :=
    { app := fun X ↦ AlgHom.toUnder (R := CommRingCat.of R)
        (toLocalColimitAlgHom (R := R) (Ω := Ω) X)
      naturality := fun X Y f ↦ by
        ext x
        exact DFunLike.congr_fun
          (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) f) x }

/-- The canonical colimit cocone and the cocone with vertex the strict local colimit are
isomorphic. -/
noncomputable def colimitCoconeIsoLocalCocone :
    colimit.cocone (functor (R := R) (Ω := Ω)) ≅ localCocone (R := R) (Ω := Ω) :=
  by
    apply Cocone.ext
      (AlgEquiv.toUnder (R := CommRingCat.of R)
        (colimitToLocalColimitAlgEquiv (R := R) (Ω := Ω)))

/-- The strict local colimit is a filtered colimit of the pointed etale neighbourhoods.  This is
the exact colimit presentation used in the `05N9` descent step of Stacks Tag `0EYG`. -/
noncomputable def localCoconeIsColimit :
    IsColimit (localCocone (R := R) (Ω := Ω)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (functor (R := R) (Ω := Ω)))
    (colimitCoconeIsoLocalCocone (R := R) (Ω := Ω))

#print axioms colimitPointPrime_primeCompl_le_isUnit
#print axioms colimitToLocalColimitAlgEquiv
#print axioms localCoconeIsColimit

end Pcf.Stacks.PointedEtaleNeighborhood
