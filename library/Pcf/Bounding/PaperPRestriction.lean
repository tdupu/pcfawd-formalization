/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyGeometry
public import Pcf.Bounding.AllCodimCoreGood

/-!
# Restricting a finite map to an integral closed subvariety

The reduced point-closure subscheme is the manuscript's integral closed
subvariety. Its image is the reduced closure of the image generic point.
This packages both conclusions of `paper-p.tex`, Lemma `lem:restriction`.
-/

@[expose] public section

namespace Pcf
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- The canonical reduced point-closure subscheme has exactly the closure
of its defining point as its underlying range. -/
theorem paperP_pointClosureSubschemeι_range {X : Scheme.{u}} (x : X) :
    Set.range (pointClosureIdealSheaf x).subschemeι = closure ({x} : Set X) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact pointClosureSubschemeι_mem x z
  · exact exists_pointClosureSubschemePoint x y

/-- The actual induced map between reduced closed subvarieties is finite
and surjective.

`paper-p.tex` correspondence: Lemma 3.2 (`lem:restriction`). -/
theorem paperP_restriction_finite_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X) :
    IsFinite (pointClosureSubschemeMap f x (f x) rfl) ∧
      Function.Surjective (pointClosureSubschemeMap f x (f x) rfl) :=
  ⟨pointClosureSubschemeMap_isFinite f x (f x) rfl,
    pointClosureSubschemeMap_surjective f x (f x) rfl⟩

/-- When the ambient finite map is dominant between integral varieties,
the image of an integral effective divisor is again an integral effective
divisor.

`paper-p.tex` correspondence: Lemma 3.2 (`lem:restriction`). -/
theorem paperP_restriction_preserves_divisor
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (P : SchemeDivisorPoint X) :
    ∃ Q : SchemeDivisorPoint Y, Q.1 = f P.1 :=
  ⟨⟨f P.1, coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sY f P⟩, rfl⟩

/-- `paper-p.tex`, Lemma `lem:restriction`, bundled for the actual reduced
image of an integral effective divisor. The finite surjective restricted
map has the image support and commuting square specified in the manuscript.
The assumption `[Surjective f]` is the manuscript's surjectivity hypothesis;
it supplies dominance for the divisor-preservation step.

`paper-p.tex` correspondence: Lemma 3.2 (`lem:restriction`). -/
theorem paperP_restriction_full
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (A : SchemeDivisorPoint X) :
    let B := pointClosureIdealSheaf (f A.1)
    let g := pointClosureSubschemeMap f A.1 (f A.1) rfl
    Order.coheight (f A.1) = 1 ∧
      IsIntegral B.subscheme ∧
      IsFinite g ∧
      Function.Surjective g ∧
      Set.range B.subschemeι =
        f '' Set.range (pointClosureIdealSheaf A.1).subschemeι ∧
      g ≫ B.subschemeι = (pointClosureIdealSheaf A.1).subschemeι ≫ f := by
  dsimp only
  refine ⟨coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sY f A, ?_,
    pointClosureSubschemeMap_isFinite f A.1 (f A.1) rfl,
    pointClosureSubschemeMap_surjective f A.1 (f A.1) rfl, ?_,
    pointClosureSubschemeMap_subschemeι f A.1 (f A.1) rfl⟩
  · exact isIntegral_of_irreducibleSpace_of_isReduced _
  · rw [paperP_pointClosureSubschemeι_range, paperP_pointClosureSubschemeι_range]
    simpa only [Set.image_singleton] using
      f.isClosedMap.closure_image_eq_of_continuous f.continuous ({A.1} : Set X)

#print axioms paperP_pointClosureSubschemeι_range
#print axioms paperP_restriction_finite_surjective
#print axioms paperP_restriction_preserves_divisor
#print axioms paperP_restriction_full

end Pcf
