/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPDictionary
public import Pcf.Bounding.TheoremAWeightedDownstairs

/-!
# A divisor that is not a branch component (`paper-p.tex`, l. 1678–1681)

The source remarks that if `B` is not a branch component, then in the proof
of `thm:bounding` every ramification index `eᵢ` equals one and the cover is
étale over `B`. The exponents `eᵢ` there are the ramification indices of the
normalization lift along the divisors above `B`. This file states the
divisor-level content: if the generic point of `B` is not a weighted branch
point of `f`, every divisor of `X̃` above `B̃` has `δ = 1`, ramification index
one, and an affine étale neighbourhood (`lem:dictionary`). The
standard-root chart of the proof itself is not restated.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

/-- **l. 1678–1681, divisor level.** If `y` is not a weighted branch point of
`f`, then over `y` the normalization lift `f̃` has `δ = 1` and ramification
index one at every source divisor, and is étale on an affine neighbourhood
of each such divisor.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem delta_eq_one_of_not_mem_weightedBranchPointSet
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (y : Y) (hy : y ∉ weightedBranchPointSet f)
    (d : SchemeDivisorPoint (Palomar.normalization X))
    (hd : Palomar.normalizationMap Y (schemeGlobalNormalizationMorphism f d.1) = y) :
    schemeDivisorDelta (schemeGlobalNormalizationMorphism f) d = 1 ∧
      schemeDivisorRamificationIdx (schemeGlobalNormalizationMorphism f) d = 1 ∧
      ∃ (U : (Palomar.normalization Y).Opens) (_ : IsAffineOpen U)
        (V : (Palomar.normalization X).Opens) (_ : IsAffineOpen V)
        (hVU : V ≤ schemeGlobalNormalizationMorphism f ⁻¹ᵁ U),
        d.1 ∈ V ∧ ((schemeGlobalNormalizationMorphism f).appLE U V hVU).hom.Etale := by
  let F := schemeGlobalNormalizationMorphism f
  have : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Y)
  have hδ : schemeDivisorDelta F d = 1 := by
    have hpos := schemeDivisorDelta_pos_of_isFinite F d
    by_contra hne
    apply hy
    rw [← hd]
    have h1 : 1 < schemeDivisorDelta F d := by omega
    exact ⟨d.mapFiniteDominantNormal F, ⟨d, rfl, h1⟩, rfl⟩
  refine ⟨hδ, ?_, (paperP_divisorDelta_eq_one_iff_etaleAt F d).mp hδ⟩
  unfold schemeDivisorDelta at hδ
  exact Nat.eq_one_of_mul_eq_one_right hδ

#print axioms delta_eq_one_of_not_mem_weightedBranchPointSet

end

end Pcf
