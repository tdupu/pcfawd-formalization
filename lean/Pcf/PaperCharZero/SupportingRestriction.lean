/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingClosedSupports

/-!
# Restriction to an integral effective divisor

A bundled formulation of `paper.tex`, Lemma `lem:restriction`. The reduced
image is the actual point-closure subscheme of the image generic point. Its
codimension, integrality, support, finite surjective restricted morphism, and
commuting square are conclusions, not additional geometric hypotheses.
The statement works over any field and therefore includes characteristic zero.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

variable {X Y : Scheme.{u}}

/-- The inclusion of the canonical reduced point closure has exactly the
closure of that point as its range. -/
theorem range_pointClosureSubschemeι (x : X) :
    Set.range (pointClosureIdealSheaf x).subschemeι = closure ({x} : Set X) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact pointClosureSubschemeι_mem x z
  · exact exists_pointClosureSubschemePoint x y

/-- `lem:restriction`: the reduced image of an integral effective divisor
under a finite dominant map is an integral effective divisor, and the actual
restriction is finite and surjective onto that reduced image.

The image divisor is represented by the actual image generic point. Both
subschemes use the canonical radical vanishing ideal of the point closure.
The equality of supports and commuting square certify that the morphism in
the conclusion is the restriction of `f`, rather than an unrelated finite map.
No normality or characteristic assumption is required. -/
theorem integral_effective_divisor_restriction
    (k : Type u) [Field k] (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)]
    (A : SchemeDivisorPoint X) :
    let B := pointClosureIdealSheaf (f A.1)
    let g := pointClosureSubschemeMap f A.1 (f A.1) rfl
    Order.coheight (f A.1) = 1 ∧
      IsIntegral B.subscheme ∧
      IsFinite g ∧
      Function.Surjective g ∧
      Set.range B.subschemeι = f '' Set.range (pointClosureIdealSheaf A.1).subschemeι ∧
      g ≫ B.subschemeι = (pointClosureIdealSheaf A.1).subschemeι ≫ f := by
  dsimp only
  refine ⟨coheight_apply_eq_one_of_finiteType f k A, ?_,
    pointClosureSubschemeMap_isFinite f A.1 (f A.1) rfl,
    pointClosureSubschemeMap_surjective f A.1 (f A.1) rfl, ?_,
    pointClosureSubschemeMap_subschemeι f A.1 (f A.1) rfl⟩
  · exact isIntegral_of_irreducibleSpace_of_isReduced _
  · rw [range_pointClosureSubschemeι, range_pointClosureSubschemeι]
    simpa only [Set.image_singleton] using
      f.isClosedMap.closure_image_eq_of_continuous f.continuous ({A.1} : Set X)

/-- The actual restriction of an ambient iterate returning a divisor to itself
is a finite surjective endomorphism of its canonical reduced integral subscheme.
The exponent may be zero; in particular the statement covers every positive
return period used by the paper. -/
theorem integral_effective_divisor_return
    (f : X ⟶ X) [IsFinite f] (A : SchemeDivisorPoint X) (m : ℕ)
    (hreturn : (End.of f ^ m).asHom A.1 = A.1) :
    let g := pointClosureSubschemeMap (End.of f ^ m).asHom A.1 A.1 hreturn
    IsIntegral (pointClosureIdealSheaf A.1).subscheme ∧
      IsFinite g ∧
      Function.Surjective g ∧
      g ≫ (pointClosureIdealSheaf A.1).subschemeι =
        (pointClosureIdealSheaf A.1).subschemeι ≫ (End.of f ^ m).asHom := by
  dsimp only
  exact ⟨isIntegral_of_irreducibleSpace_of_isReduced _,
    pointClosureSubschemeMap_isFinite (End.of f ^ m).asHom A.1 A.1 hreturn,
    pointClosureSubschemeMap_surjective (End.of f ^ m).asHom A.1 A.1 hreturn,
    pointClosureSubschemeMap_subschemeι (End.of f ^ m).asHom A.1 A.1 hreturn⟩

end Pcf.PaperCharZero
