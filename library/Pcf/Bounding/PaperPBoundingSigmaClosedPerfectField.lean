/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingStepZero
public import Pcf.Bounding.SingularLocusClosedPerfectField

/-!
# The exceptional set of `thm:bounding` is proper and closed over a perfect field

`paper-p.tex`, Theorem `thm:bounding`, Step 0, asserts that
`Σ = (B ∩ Z) ∪ (B ∩ Sing Y) ∪ Sing B` is a proper closed subset of `B`.
The closedness hypotheses of
`paperPBoundingSigma_closed_proper_finite_of_singularClosed` are discharged here
by `isClosed_stalkSingularLocus_of_perfectField`, with no codimension-one
restriction on the singular points.

Scope: the base field is assumed perfect (this covers characteristic zero).
The manuscript allows an arbitrary field `k`; the imperfect case needs the
full J-2 property of Stacks `07R5`, which is not proved here.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- The singular locus of the reduced closed subscheme on the closure of a point
of a scheme locally of finite type over a perfect field is closed. -/
theorem isClosed_stalkSingularLocus_pointClosure_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (y : Y) :
    IsClosed (stalkSingularLocus (pointClosureIdealSheaf y).subscheme) :=
  isClosed_stalkSingularLocus_of_perfectField k ((pointClosureIdealSheaf y).subschemeι ≫ s)

/-- `paper-p.tex`, `thm:bounding`, Step 0, over a perfect base field: the exact
exceptional set `Σ = (B ∩ Z) ∪ (B ∩ Sing Y) ∪ Sing B` is closed and proper, and
so contains only finitely many divisor generic points. -/
theorem paperPBoundingSigma_closed_proper_finite_of_perfectField
    (k : Type u) [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme Y] [NoetherianSpace X] [NoetherianSpace Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparableSchemeMap f)
    (B : SchemeDivisorPoint Y) :
    IsClosed (paperPBoundingSigma f B) ∧
      paperPBoundingSigma f B ≠ Set.univ ∧
      {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
        closure ({Q.1} : Set (pointClosureIdealSheaf B.1).subscheme) ⊆
          paperPBoundingSigma f B}.Finite :=
  paperPBoundingSigma_closed_proper_finite_of_singularClosed k s f hsep B
    (isClosed_stalkSingularLocus_of_perfectField k s)
    (isClosed_stalkSingularLocus_pointClosure_of_perfectField k s B.1)

/-- The bounding-data form of Step 0 over a perfect field: for a finite dominant
map with monodromy not divisible by `p` and an integral divisor `A` of `X`
with image `B`, the exact `Σ` on `B` is a proper closed subset. Here `p` is any
natural number (`p = 0` is the characteristic-zero case). -/
theorem paperPBoundingSigma_closed_proper_finite_of_primeToPMonodromy_of_perfectField
    (p : ℕ) (k : Type u) [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    IsClosed (paperPBoundingSigma f (A.mapFiniteDominantNormal f)) ∧
      paperPBoundingSigma f (A.mapFiniteDominantNormal f) ≠ Set.univ ∧
      {Q : SchemeDivisorPoint
          (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme |
        closure ({Q.1} : Set
          (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) ⊆
          paperPBoundingSigma f (A.mapFiniteDominantNormal f)}.Finite := by
  let : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  let : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  exact paperPBoundingSigma_closed_proper_finite_of_perfectField k s f
    (isGenericallySeparableSchemeMap_of_primeToPMonodromyMap p f hmono)
    (A.mapFiniteDominantNormal f)

#print axioms isClosed_stalkSingularLocus_pointClosure_of_perfectField
#print axioms paperPBoundingSigma_closed_proper_finite_of_perfectField
#print axioms paperPBoundingSigma_closed_proper_finite_of_primeToPMonodromy_of_perfectField

end Pcf
