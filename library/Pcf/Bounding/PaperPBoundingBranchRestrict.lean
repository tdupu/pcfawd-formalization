/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingBranchContainment
public import Pcf.Bounding.PaperPBlowupBranchOpenRestriction

/-!
# The branch locus over an open subset

`paper-p.tex`, proof of `thm:bounding`, Step 0: "The branch locus of `f` over `U` is
`branch(f) ∩ U`, since both ramification indices and residue-field inseparability are
unchanged on restriction to open subsets."

For the actual open restriction `f ∣_ U : f⁻¹U → U` of a finite surjective morphism of normal
varieties, `branch(f ∣_ U) = U ∩ branch(f)` (as a subset of `U`, and after pushing forward
along `U ↪ Y`). This uses the source-divisor description of the weighted branch locus of a
normal cover (`weightedBranchPointSet_open_pullback`) and that closures commute with preimages
under open embeddings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- An open subscheme of a normal scheme is normal. -/
theorem isNormalScheme_opens {X : Scheme.{u}} [IsNormalScheme X] (U : X.Opens) :
    IsNormalScheme U.toScheme where
  component_integrallyClosed W := by
    haveI := IsNormalScheme.component_integrallyClosed
      (X := X) ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩
    exact IsIntegrallyClosed.of_equiv (U.ι.appIso W).commRingCatIsoToRingEquiv

/-- The restriction of a surjective morphism over an open is surjective. -/
instance surjective_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (U : Y.Opens) : Surjective (f ∣_ U) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹Surjective f›

/-- The weighted branch locus of a finite dominant map of normal schemes commutes with
restriction along an open pullback square. -/
theorem weightedBranchLocus_open_pullback
    {U V X Y : Scheme.{u}}
    [IsIntegral U] [IsIntegral V] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme U] [IsNormalScheme V] [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap U)] [IsFinite (Palomar.normalizationMap V)]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (g : U ⟶ V) (i : U ⟶ X) (j : V ⟶ Y) (f : X ⟶ Y)
    [IsFinite g] [IsDominant g] [IsFinite f] [IsDominant f]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (h : IsPullback g i j f) :
    weightedBranchLocus g = j ⁻¹' weightedBranchLocus f := by
  rw [weightedBranchLocus, weightedBranchLocus,
    Bounding.AllCodimBlowup.weightedBranchPointSet_open_pullback g i j f h,
    j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous]

namespace PaperPBoundingData

variable {k : Type u} [Field k] (D : PaperPBoundingData k)

/-- **`thm:bounding`, Step 0: the branch locus of `f` over `U` is `branch(f) ∩ U`.**
For a nonempty open `U ⊆ Y` and the actual restriction `f ∣_ U : f⁻¹U → U`,
the branch locus of `f ∣_ U` is the preimage of `branch(f)` in `U`, and its image in `Y`
is `branch(f) ∩ U`. -/
theorem branch_restrict_eq (U : D.Y.Opens) [Nonempty U] :
    haveI : Nonempty (D.f ⁻¹ᵁ U) := by
      obtain ⟨y⟩ := ‹Nonempty U›
      obtain ⟨x, hx⟩ := D.f.surjective y.1
      exact ⟨⟨x, show D.f x ∈ U by rw [hx]; exact y.2⟩⟩
    letI : IsFinite (Palomar.normalizationMap U.toScheme) :=
      schemeGlobalNormalizationMap_isFinite U.toScheme k (U.ι ≫ D.s)
    letI : IsFinite (Palomar.normalizationMap (D.f ⁻¹ᵁ U).toScheme) :=
      schemeGlobalNormalizationMap_isFinite (D.f ⁻¹ᵁ U).toScheme k
        ((D.f ⁻¹ᵁ U).ι ≫ D.f ≫ D.s)
    weightedBranchLocus (D.f ∣_ U) = U.ι ⁻¹' weightedBranchLocus D.f ∧
      U.ι '' weightedBranchLocus (D.f ∣_ U) = weightedBranchLocus D.f ∩ U := by
  haveI : Nonempty (D.f ⁻¹ᵁ U) := by
    obtain ⟨y⟩ := ‹Nonempty U›
    obtain ⟨x, hx⟩ := D.f.surjective y.1
    exact ⟨⟨x, show D.f x ∈ U by rw [hx]; exact y.2⟩⟩
  letI : IsFinite (Palomar.normalizationMap U.toScheme) :=
    schemeGlobalNormalizationMap_isFinite U.toScheme k (U.ι ≫ D.s)
  letI : IsFinite (Palomar.normalizationMap (D.f ⁻¹ᵁ U).toScheme) :=
    schemeGlobalNormalizationMap_isFinite (D.f ⁻¹ᵁ U).toScheme k
      ((D.f ⁻¹ᵁ U).ι ≫ D.f ≫ D.s)
  haveI := isNormalScheme_opens U
  haveI := isNormalScheme_opens (D.f ⁻¹ᵁ U)
  have h1 := weightedBranchLocus_open_pullback (D.f ∣_ U) (D.f ⁻¹ᵁ U).ι U.ι D.f
    (isPullback_morphismRestrict D.f U)
  refine ⟨h1, ?_⟩
  rw [h1, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]

end PaperPBoundingData

end

#print axioms isNormalScheme_opens
#print axioms weightedBranchLocus_open_pullback
#print axioms PaperPBoundingData.branch_restrict_eq

end Pcf
