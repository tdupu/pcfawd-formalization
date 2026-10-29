/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingStepZero
public import Pcf.Bounding.PaperPRestriction

/-!
# Bounding data

`paper-p.tex`, Definition `def:bounding-data`: a finite surjective morphism
`f : X → Y` of normal varieties, an integral effective divisor `A ⊆ X`, its
image `B = f(A)`, the restriction `g = f|_A : A → B` of `lem:restriction`, and
the union `Z` of the components of `branch(f)` other than `B`.

The Lean `Z` is `paperPBoundingOtherBranch f B`, the closure of the weighted
branch generic points other than `B`. The existing theorem
`paperPBoundingOtherBranch_eq_other_components` identifies it with the
union of the actual irreducible components of the weighted branch locus
other than the closure of `B`, which is the manuscript's wording.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf

universe u
noncomputable section

/-- `paper-p.tex`, Definition `def:bounding-data`. The data are a finite
surjective morphism `f : X → Y` of normal varieties over `k` and an integral
effective divisor `A` of `X`; the remaining fields `B`, `g`, `Z` are the
derived declarations below. A variety is an integral, Noetherian scheme
locally of finite type over `k`.

`paper-p.tex` correspondence: Definition 7.4 (`def:bounding-data`). -/
structure PaperPBoundingData (k : Type u) [Field k] where
  /-- The source variety. -/
  X : Scheme.{u}
  /-- The target variety. -/
  Y : Scheme.{u}
  [isIntegral_X : IsIntegral X]
  [isIntegral_Y : IsIntegral Y]
  [isNormal_X : IsNormalScheme X]
  [isNormal_Y : IsNormalScheme Y]
  [isLocallyNoetherian_X : IsLocallyNoetherian X]
  [isLocallyNoetherian_Y : IsLocallyNoetherian Y]
  [noetherianSpace_X : NoetherianSpace X]
  [noetherianSpace_Y : NoetherianSpace Y]
  /-- The structure morphism of the target. -/
  s : Y ⟶ Spec (.of k)
  [locallyOfFiniteType_s : LocallyOfFiniteType s]
  /-- The finite surjective morphism. -/
  f : X ⟶ Y
  [isFinite_f : IsFinite f]
  [surjective_f : Surjective f]
  /-- The integral effective divisor of the source. -/
  A : SchemeDivisorPoint X

namespace PaperPBoundingData

attribute [instance] isIntegral_X isIntegral_Y isNormal_X isNormal_Y
  isLocallyNoetherian_X isLocallyNoetherian_Y noetherianSpace_X noetherianSpace_Y
  locallyOfFiniteType_s isFinite_f surjective_f

variable {k : Type u} [Field k] (D : PaperPBoundingData k)

instance : IsDominant D.f := inferInstance

instance : IsFinite (Palomar.normalizationMap D.X) :=
  schemeGlobalNormalizationMap_isFinite D.X k (D.f ≫ D.s)

instance : IsFinite (Palomar.normalizationMap D.Y) :=
  schemeGlobalNormalizationMap_isFinite D.Y k D.s

/-- The image divisor `B = f(A)`.

`paper-p.tex` correspondence: Definition 7.4 (`def:bounding-data`). -/
def B : SchemeDivisorPoint D.Y := D.A.mapFiniteDominantNormal D.f

/-- The restriction `g = f|_A : A → B` between the reduced point closures. -/
def g : (pointClosureIdealSheaf D.A.1).subscheme ⟶
    (pointClosureIdealSheaf (D.f D.A.1)).subscheme :=
  pointClosureSubschemeMap D.f D.A.1 (D.f D.A.1) rfl

/-- The union `Z` of the weighted branch components other than `B`. -/
def Z : Set D.Y := paperPBoundingOtherBranch D.f D.B

theorem B_val : D.B.1 = D.f D.A.1 := rfl

/-- The fields `B` and `g` are those of `lem:restriction`. -/
theorem restriction :
    Order.coheight (D.f D.A.1) = 1 ∧
      IsIntegral (pointClosureIdealSheaf (D.f D.A.1)).subscheme ∧
      IsFinite D.g ∧ Function.Surjective D.g ∧
      Set.range (pointClosureIdealSheaf (D.f D.A.1)).subschemeι =
        D.f '' Set.range (pointClosureIdealSheaf D.A.1).subschemeι ∧
      D.g ≫ (pointClosureIdealSheaf (D.f D.A.1)).subschemeι =
        (pointClosureIdealSheaf D.A.1).subschemeι ≫ D.f :=
  paperP_restriction_full k D.s D.f D.A

/-- The field `Z` is the union of the branch components other than `B`. -/
theorem Z_eq_sUnion_components (hsep : IsGenericallySeparableSchemeMap D.f) :
    D.Z = ⋃₀ {C | C ∈ relativeIrreducibleComponents (weightedBranchLocus D.f) ∧
      C ≠ closure ({D.B.1} : Set D.Y)} :=
  paperPBoundingOtherBranch_eq_other_components k D.s D.f hsep D.B

end PaperPBoundingData

end

#print axioms PaperPBoundingData.restriction
#print axioms PaperPBoundingData.Z_eq_sUnion_components

end Pcf
