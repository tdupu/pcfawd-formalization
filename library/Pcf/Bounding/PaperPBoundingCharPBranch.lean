/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingCharPPointwise
public import Pcf.Bounding.PaperPBoundingFiniteSingularCharP
public import Pcf.Unnormalized.SchemeBranch

/-!
# Branch-locus conclusion of positive-characteristic bounding

The actual `i = 1` branch predicate of the original reduced divisor
restriction is supported on the exact `Σ` of `paper-p.tex`, `thm:bounding`.
Because only finitely many divisor generic points lie in `Σ`, the branch
predicate is finite in positive characteristic.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The original restricted map is étale over every divisor generic point
outside the exact manuscript exceptional set. Thus its `i = 1` branch
predicate is contained in the divisor points of that set.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharP_branchOne_subset_Sigma
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
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
    schemeUnnormalizedBranchOne (A.closureMapFiniteDominantNormal f) ⊆
      {Q : SchemeDivisorPoint
        (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme |
          Q.1 ∈ paperPBoundingSigma f (A.mapFiniteDominantNormal f)} := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  intro Q hQ
  obtain ⟨x, hx, hnot⟩ := hQ
  by_contra hbad
  exact hnot (paperPBoundingCharP_at_formallyEtale p hp k s f hmono A x Q hx hbad)

/-- The `i = 1` branch divisors of the original reduced restriction are
finite for a prime-to-`p` normal finite cover, over any characteristic-`p`
field. The branch set itself is the exact manuscript predicate.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharP_branchOne_finite
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X) :
    (schemeUnnormalizedBranchOne (A.closureMapFiniteDominantNormal f)).Finite := by
  exact (paperPBoundingSigma_badDivisors_finite_charP p hp k s f hmono A).subset
    (paperPBoundingCharP_branchOne_subset_Sigma p hp k s f hmono A)

#print axioms paperPBoundingCharP_branchOne_subset_Sigma
#print axioms paperPBoundingCharP_branchOne_finite

end
end Pcf
