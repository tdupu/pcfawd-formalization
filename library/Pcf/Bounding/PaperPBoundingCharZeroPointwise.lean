/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingIncidence
public import Pcf.Bounding.PaperPBoundingCoveringInputs
public import Pcf.Bounding.DivisorFlagCodimension

/-!
# Characteristic-zero pointwise bounding for the original divisor restriction

For the exact exceptional set `Σ` of `paper-p.tex`, Theorem `thm:bounding`,
this module constructs the local purity--Abhyankar chart of the original
reduced divisor restriction at a selected source point over each good target
integral effective divisor. The full theorem requires the same conclusion
for every source divisor above that target divisor.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Every point of the original reduced source divisor above a good target
integral effective divisor has a formally étale stalk. This uses the actual
finite restriction, with no chosen source point in the fiber.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharZero_at_formallyEtale
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hxz : A.closureMapFiniteDominantNormal f x = z.1) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    z.1 ∉ paperPBoundingSigma f (A.mapFiniteDominantNormal f) →
      ((A.closureMapFiniteDominantNormal f).stalkMap x).hom.FormallyEtale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  intro hz
  let B := A.mapFiniteDominantNormal f
  let I := pointClosureIdealSheaf A.1
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f := pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 rfl
  have hreg := paperPBoundingSigma_regular_at f B z.1 hz
  let hex := exists_isAffineOpen_mem_and_subset
    (show J.subschemeι z.1 ∈ (⊤ : Y.Opens) by trivial)
  let U : Y.affineOpens := ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  have hzU : J.subschemeι z.1 ∈ (U : Y.Opens) :=
    (Classical.choose_spec hex).2.1
  letI : Algebra ℚ Γ(Y, U) := schemeAffineRationalAlgebraOfField k s U
  have hsquare : J.subschemeι (A.closureMapFiniteDominantNormal f x) =
      f (I.subschemeι x) := by
    change (I.subschemeMap J f H ≫ J.subschemeι) x = (I.subschemeι ≫ f) x
    rw [I.subschemeMap_subschemeι J f H]
  have hx : x ∈ I.subschemeι ⁻¹ᵁ (finitePreimageAffine f U : X.Opens) := by
    change f (I.subschemeι x) ∈ (U : Y.Opens)
    rw [← hsquare, hxz]
    exact hzU
  letI : Nonempty (U : Y.Opens) := ⟨⟨J.subschemeι z.1, hzU⟩⟩
  letI : Nonempty (finitePreimageAffine f U : X.Opens) :=
    ⟨⟨I.subschemeι x, hx⟩⟩
  have hbranch :
      (⟨J.subschemeι z.1, hzU⟩ : (U : Y.Opens)) ∉
        finiteAffineOtherBranchLocus (f := f) U
          (affinePrimeOfSchemeDivisorPoint B U
            (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)) := by
    exact paperPBoundingSigma_avoids_affineOtherBranch f B z.1 U hzU hz
  have hchart :=
    A.closureStalkBoundingLocalizationOfCorrectionRegularDimTwoAt
      f U x hx z hzU hxz
      (B.closureDivisor_coheight_of_finiteType k s z)
      hreg.1 hreg.2 hbranch
      (Stacks.zariskiNagataPurity _ _)
      (Stacks.abhyankarLemma _ _ _)
  exact hchart.formallyEtale

/-- The formal stalk conclusion above gives actual étale affine
neighborhoods of every specified point over a good target divisor point.
Finiteness of the original restriction supplies local finite presentation.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharZero_at_etaleNeighborhood
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hxz : A.closureMapFiniteDominantNormal f x = z.1) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    let g := A.closureMapFiniteDominantNormal f
    z.1 ∉ paperPBoundingSigma f (A.mapFiniteDominantNormal f) →
      ∃ (U : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme.Opens)
        (_ : IsAffineOpen U)
        (V : (pointClosureIdealSheaf A.1).subscheme.Opens)
        (_ : IsAffineOpen V)
        (hVU : V ≤ g ⁻¹ᵁ U),
        x ∈ V ∧ (g.appLE U V hVU).hom.Etale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  let g := A.closureMapFiniteDominantNormal f
  dsimp only
  intro hz
  letI : IsFinite g := pointClosureSubschemeMap_isFinite f A.1
    (A.mapFiniteDominantNormal f).1 rfl
  letI : LocallyOfFinitePresentation g := by infer_instance
  exact exists_etale_of_formallyEtale_stalk g x
    (paperPBoundingCharZero_at_formallyEtale k s f A x z hxz hz)

/-- The actual original-scheme restriction has a formally étale stalk at the
canonical selected point over every target divisor point outside `Σ`. -/
theorem paperPBoundingCharZero_selected_formallyEtale
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X)
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    z.1 ∉ paperPBoundingSigma f (A.mapFiniteDominantNormal f) →
    let x := A.closurePreimageFiniteDominantNormal f z.1
    ((A.closureMapFiniteDominantNormal f).stalkMap x).hom.FormallyEtale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  intro hz
  let B := A.mapFiniteDominantNormal f
  let x := A.closurePreimageFiniteDominantNormal f z.1
  have hreg := paperPBoundingSigma_regular_at f B z.1 hz
  let hex := exists_isAffineOpen_mem_and_subset
    (show (pointClosureIdealSheaf B.1).subschemeι z.1 ∈ (⊤ : Y.Opens) by trivial)
  let U : Y.affineOpens := ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  have hzU : (pointClosureIdealSheaf B.1).subschemeι z.1 ∈ (U : Y.Opens) :=
    (Classical.choose_spec hex).2.1
  letI : Algebra ℚ Γ(Y, U) := schemeAffineRationalAlgebraOfField k s U
  have hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens) :=
    A.closurePreimage_mem_finitePreimage f U z.1 hzU
  letI : Nonempty (U : Y.Opens) :=
    ⟨⟨(pointClosureIdealSheaf B.1).subschemeι z.1, hzU⟩⟩
  letI : Nonempty (finitePreimageAffine f U : X.Opens) :=
    ⟨⟨(pointClosureIdealSheaf A.1).subschemeι x, hx⟩⟩
  have hbranch :
      (⟨(pointClosureIdealSheaf B.1).subschemeι z.1, hzU⟩ : (U : Y.Opens)) ∉
        finiteAffineOtherBranchLocus (f := f) U
          (affinePrimeOfSchemeDivisorPoint B U
            (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)) := by
    exact paperPBoundingSigma_avoids_affineOtherBranch f B z.1 U hzU hz
  have hchart :=
    A.closureStalkBoundingLocalizationOfCorrectionRegularDimTwoAt
      f U x hx z hzU (A.closureMap_preimageFiniteDominantNormal f z.1)
      (B.closureDivisor_coheight_of_finiteType k s z)
      hreg.1 hreg.2 hbranch
      (Stacks.zariskiNagataPurity _ _)
      (Stacks.abhyankarLemma _ _ _)
  exact hchart.formallyEtale

#print axioms paperPBoundingCharZero_at_formallyEtale
#print axioms paperPBoundingCharZero_at_etaleNeighborhood
#print axioms paperPBoundingCharZero_selected_formallyEtale

end
end Pcf
