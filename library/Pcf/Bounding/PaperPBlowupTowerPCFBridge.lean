/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupFiniteWActualAffine
public import Pcf.Bounding.PaperPTower.Normalized

/-!
# From normalized tower PCF to the affine cover branch family

An affine presentation identifies each packaged cover's original branch
image with the corresponding tower composite's branch support, transported
to `Spec R`. The comparison is kept explicit until global affine
presentation and blow-up gluing are available.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

/-- An explicit branch-support comparison transports normalized PCF of the
source tower into the finite original affine family needed to construct W.
The comparison is the remaining affine-presentation datum for a general
nonaffine tower. -/
theorem NormalAffineFiniteCover.originalBranchImages_finite_of_towerPCF
    (k : Type u) [Field k]
    (T : Pcf.PaperPTower.Tower k) (hpcf : T.IsNormalizedPCF)
    {R : Type u} [CommRing R]
    (C : ℕ → NormalAffineFiniteCover R)
    (e : T.X 0 ⟶ Spec (.of R))
    (hbranchComparison : ∀ n,
      schemeDivisorBranchImage (C n).specMap ⊆
        e '' T.normalizedBranchGenericPoints (n + 1)) :
    (⋃ n, schemeDivisorBranchImage (C n).specMap).Finite := by
  have hsub : (⋃ n, schemeDivisorBranchImage (C n).specMap) ⊆
      e '' (⋃ n, T.normalizedBranchGenericPoints (n + 1)) := by
    intro y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx, hxy⟩ := hbranchComparison n hn
    exact ⟨x, Set.mem_iUnion.mpr ⟨n, hx⟩, hxy⟩
  exact (hpcf.image e).subset hsub

/-- With an affine branch-support presentation, normalized PCF of a tower
produces the fixed finite W on the actual normalized Rees blow-up. -/
theorem NormalAffineFiniteCover.normalizedReesTowerW_finite_of_towerPCF
    (k : Type u) [Field k]
    (T : Pcf.PaperPTower.Tower k) (hpcf : T.IsNormalizedPCF)
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (e : T.X 0 ⟶ Spec (.of R))
    (hbranchComparison : ∀ n,
      schemeDivisorBranchImage (C n).specMap ⊆
        e '' T.normalizedBranchGenericPoints (n + 1)) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (normalizedReesTowerW I a ha C).Finite) := by
  exact normalizedReesTowerW_finite_of_pcf k I hI a ha C
    (originalBranchImages_finite_of_towerPCF k T hpcf C e hbranchComparison)

#print axioms NormalAffineFiniteCover.originalBranchImages_finite_of_towerPCF
#print axioms NormalAffineFiniteCover.normalizedReesTowerW_finite_of_towerPCF

end
end Pcf.Bounding.AllCodimBlowup
