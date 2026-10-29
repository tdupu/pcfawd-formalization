/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupBranchImageWeighted
public import Pcf.Bounding.PaperPBlowupAffineCoverFiniteness
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Branch support on open charts

The branch generic points used in the normalized blow-up argument of
`paper-p.tex`, Theorem `thm:tower-restrict`, commute with restriction to an
open target and its full inverse image. The comparison is proved from
stalk isomorphisms and preservation of codimension under open immersions.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

/-- An open chart square identifies formal étaleness of the two maps at
corresponding source points. -/
theorem formallyEtale_stalkMap_iff_of_open_square
    {U V X Y : Scheme.{u}} (g : U ⟶ V) (i : U ⟶ X)
    (j : V ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : g ≫ j = i ≫ f) (x : U) :
    (g.stalkMap x).hom.FormallyEtale ↔ (f.stalkMap (i x)).hom.FormallyEtale :=
  Pcf.formallyEtale_stalkMap_iff_of_square g i j f h x
    (ConcreteCategory.bijective_of_isIso (i.stalkMap x))
    (ConcreteCategory.bijective_of_isIso (j.stalkMap (g x)))

/-- Branch images on an open source chart map into the ambient branch
image. This direction requires only a commuting open square. -/
theorem schemeDivisorBranchImage_open_square_subset
    {U V X Y : Scheme.{u}} (g : U ⟶ V) (i : U ⟶ X)
    (j : V ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : g ≫ j = i ≫ f) :
    schemeDivisorBranchImage g ⊆ j ⁻¹' schemeDivisorBranchImage f := by
  rintro y ⟨d, hd, rfl⟩
  let e : SchemeDivisorPoint X :=
    ⟨i d.1, (coheight_eq_of_isOpenImmersion (x := d.1) i).trans d.2⟩
  refine ⟨e, ?_, ?_⟩
  · exact (formallyEtale_stalkMap_iff_of_open_square g i j f h d.1).not.mp hd
  · exact (congrArg (fun m => m d.1) h).symm

/-- If the source chart is the full inverse image of the target chart,
branch generic points are exactly the preimage of the global branch set.
No normality or finiteness assumption is needed for this non-étale
source-divisor formulation. -/
theorem schemeDivisorBranchImage_open_pullback
    {U V X Y : Scheme.{u}} (g : U ⟶ V) (i : U ⟶ X)
    (j : V ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : IsPullback g i j f) :
    schemeDivisorBranchImage g = j ⁻¹' schemeDivisorBranchImage f := by
  apply Set.Subset.antisymm (schemeDivisorBranchImage_open_square_subset g i j f h.w)
  rintro y ⟨d, hd, hdy⟩
  obtain ⟨x, hxg, hxi⟩ := Scheme.exists_preimage_of_isPullback h y d.1 hdy.symm
  let e : SchemeDivisorPoint U :=
    ⟨x, (coheight_eq_of_isOpenImmersion (x := x) i).symm.trans (hxi.symm ▸ d.2)⟩
  refine ⟨e, ?_, hxg⟩
  apply (formallyEtale_stalkMap_iff_of_open_square g i j f h.w x).not.mpr
  change ¬ (f.stalkMap d.1).hom.FormallyEtale at hd
  change i x = d.1 at hxi
  rw [hxi]
  exact hd

/-- The canonical restriction of a scheme morphism to an open target
has precisely the restricted branch generic points. -/
theorem schemeDivisorBranchImage_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    schemeDivisorBranchImage (f ∣_ V) = V.ι ⁻¹' schemeDivisorBranchImage f :=
  schemeDivisorBranchImage_open_pullback (f ∣_ V) (f ⁻¹ᵁ V).ι V.ι f
    (isPullback_morphismRestrict f V)

/-- The branch image of the actual categorical base change to an open
chart is the preimage of the branch image downstairs. -/
theorem schemeDivisorBranchImage_pullback_open
    {X Y V : Scheme.{u}} (f : X ⟶ Y) (j : V ⟶ Y) [IsOpenImmersion j] :
    schemeDivisorBranchImage (Limits.pullback.snd f j) =
      j ⁻¹' schemeDivisorBranchImage f :=
  schemeDivisorBranchImage_open_pullback (Limits.pullback.snd f j)
    (Limits.pullback.fst f j) j f (IsPullback.of_hasPullback f j).flip

/-- Finiteness of the branch union for an arbitrary family is equivalent
to finiteness of the actual base-changed branch unions on a finite open
cover. The chartwise identification is proved, rather than assumed. -/
theorem finite_union_branchImage_iff_finite_openCover
    {Y : Scheme.{u}} (X : ℕ → Scheme.{u}) (f : ∀ n, X n ⟶ Y)
    (𝒰 : Y.OpenCover) [Finite 𝒰.I₀] :
    (⋃ n, schemeDivisorBranchImage (f n)).Finite ↔
      ∀ i : 𝒰.I₀,
        (⋃ n, schemeDivisorBranchImage (Limits.pullback.snd (f n) (𝒰.f i))).Finite := by
  have heq : ∀ i : 𝒰.I₀,
      (⋃ n, schemeDivisorBranchImage (Limits.pullback.snd (f n) (𝒰.f i))) =
        𝒰.f i ⁻¹' (⋃ n, schemeDivisorBranchImage (f n)) := by
    intro i
    simp only [schemeDivisorBranchImage_pullback_open, Set.preimage_iUnion]
  simp_rw [heq]
  constructor
  · intro h i
    exact Set.Finite.preimage (𝒰.f i).isOpenEmbedding.injective.injOn h
  · exact finite_of_finite_on_finite_openCover 𝒰 _

/-- The canonical affine-cover criterion for a quasi-compact target,
expressed entirely using the actual maps on the inverse-image charts. -/
theorem finite_union_branchImage_iff_affineCover
    {Y : Scheme.{u}} [CompactSpace Y]
    (X : ℕ → Scheme.{u}) (f : ∀ n, X n ⟶ Y) :
    (⋃ n, schemeDivisorBranchImage (f n)).Finite ↔
      ∀ i : Y.affineCover.I₀,
        (⋃ n, schemeDivisorBranchImage
          (Limits.pullback.snd (f n) (Y.affineCover.f i))).Finite := by
  have heq : ∀ i : Y.affineCover.I₀,
      (⋃ n, schemeDivisorBranchImage
        (Limits.pullback.snd (f n) (Y.affineCover.f i))) =
        Y.affineCover.f i ⁻¹' (⋃ n, schemeDivisorBranchImage (f n)) := by
    intro i
    simp only [schemeDivisorBranchImage_pullback_open, Set.preimage_iUnion]
  simp_rw [heq]
  constructor
  · intro h i
    exact Set.Finite.preimage (Y.affineCover.f i).isOpenEmbedding.injective.injOn h
  · exact finite_of_finite_on_affineCover Y _

/-- On finite dominant normal covers, the manuscript's weighted branch
support commutes with restriction to a full inverse-image open chart. -/
theorem weightedBranchPointSet_open_pullback
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
    weightedBranchPointSet g = j ⁻¹' weightedBranchPointSet f := by
  rw [weightedBranchPointSet_eq_schemeDivisorBranchImage,
    weightedBranchPointSet_eq_schemeDivisorBranchImage]
  exact schemeDivisorBranchImage_open_pullback g i j f h

/-- Normalized PCF of a normal tower can be tested using its actual
composites on the canonical affine charts of the base. This is an exact
geometric specialization of the local-to-global branch criterion. -/
theorem tower_isNormalizedPCF_iff_affineCover
    (k : Type u) [Field k] (T : Pcf.PaperPTower.Tower k)
    [∀ n, IsNormalScheme (T.X n)] :
    T.IsNormalizedPCF ↔
      ∀ i : (T.X 0).affineCover.I₀,
        (⋃ n, schemeDivisorBranchImage
          (Limits.pullback.snd (T.composite (n + 1))
            ((T.X 0).affineCover.f i))).Finite := by
  have heq : ∀ n,
      T.normalizedBranchGenericPoints (n + 1) =
        schemeDivisorBranchImage (T.composite (n + 1)) := by
    intro n
    rw [T.normalizedBranchGenericPoints_eq_weighted,
      weightedBranchPointSet_eq_schemeDivisorBranchImage]
  unfold Pcf.PaperPTower.Tower.IsNormalizedPCF
  simp_rw [heq]
  exact finite_union_branchImage_iff_affineCover (fun n => T.X (n + 1))
    (fun n => T.composite (n + 1))

/-- An actual affine chart of every positive composite of a normal PCF
tower has finite total branch image. The input is a commuting square of
open immersions; there is no assumed branch-support comparison. -/
theorem NormalAffineFiniteCover.originalBranchImages_finite_of_open_towerCharts
    (k : Type u) [Field k] (T : Pcf.PaperPTower.Tower k)
    [∀ n, IsNormalScheme (T.X n)] (hpcf : T.IsNormalizedPCF)
    {R : Type u} [CommRing R] (C : ℕ → NormalAffineFiniteCover R)
    (j : Spec (.of R) ⟶ T.X 0) [IsOpenImmersion j]
    (i : ∀ n, Spec (.of (C n).S) ⟶ T.X (n + 1))
    [∀ n, IsOpenImmersion (i n)]
    (hcomm : ∀ n, (C n).specMap ≫ j = i n ≫ T.composite (n + 1)) :
    (⋃ n, schemeDivisorBranchImage (C n).specMap).Finite := by
  have hsub : (⋃ n, schemeDivisorBranchImage (C n).specMap) ⊆
      j ⁻¹' (⋃ n, T.normalizedBranchGenericPoints (n + 1)) := by
    intro y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    have hbranch := schemeDivisorBranchImage_open_square_subset
      (C n).specMap (i n) j (T.composite (n + 1)) (hcomm n) hn
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [T.normalizedBranchGenericPoints_eq_weighted,
      weightedBranchPointSet_eq_schemeDivisorBranchImage]
    exact hbranch
  exact (Set.Finite.preimage j.isOpenEmbedding.injective.injOn hpcf).subset hsub

/-- The fixed finite branch family on the actual normalized Rees target
is obtained from open chart presentations of a normal PCF tower. This
removes the branch-comparison hypothesis of the earlier affine bridge. -/
theorem NormalAffineFiniteCover.normalizedReesTowerW_finite_of_open_towerCharts
    (k : Type u) [Field k] (T : Pcf.PaperPTower.Tower k)
    [∀ n, IsNormalScheme (T.X n)] (hpcf : T.IsNormalizedPCF)
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (j : Spec (.of R) ⟶ T.X 0) [IsOpenImmersion j]
    (i : ∀ n, Spec (.of (C n).S) ⟶ T.X (n + 1))
    [∀ n, IsOpenImmersion (i n)]
    (hcomm : ∀ n, (C n).specMap ≫ j = i n ≫ T.composite (n + 1)) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (normalizedReesTowerW I a ha C).Finite) := by
  exact normalizedReesTowerW_finite_of_pcf k I hI a ha C
    (originalBranchImages_finite_of_open_towerCharts k T hpcf C j i hcomm)

#print axioms tower_isNormalizedPCF_iff_affineCover
#print axioms schemeDivisorBranchImage_morphismRestrict
#print axioms schemeDivisorBranchImage_pullback_open
#print axioms finite_union_branchImage_iff_finite_openCover
#print axioms finite_union_branchImage_iff_affineCover
#print axioms weightedBranchPointSet_open_pullback
#print axioms NormalAffineFiniteCover.originalBranchImages_finite_of_open_towerCharts
#print axioms NormalAffineFiniteCover.normalizedReesTowerW_finite_of_open_towerCharts
#print axioms formallyEtale_stalkMap_iff_of_open_square
#print axioms schemeDivisorBranchImage_open_square_subset
#print axioms schemeDivisorBranchImage_open_pullback

end
end Pcf.Bounding.AllCodimBlowup
