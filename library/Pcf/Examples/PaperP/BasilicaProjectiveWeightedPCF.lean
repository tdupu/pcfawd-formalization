/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaProjectivePCF
public import Pcf.Bounding.PaperPProjectiveNormal
public import Pcf.Bounding.PaperPIteration
public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.PaperPDictionary

/-!
# Full normalized weighted PCF for the projective basilica map

This completes the scheme and normalized divisor claims of
`latex/paper-p.tex`, Example `ex:basilica`, over any field in which `2` is
nonzero. The actual global map is finite, surjective and generically
separable. Its actual `Spec k` structure map is of finite type. The
normalization-weighted critical locus is `{0, ∞}`, the branch locus is
`{-1, ∞}`, and the normalized postcritical point set is `{0, -1, ∞}`.
In particular the manuscript's existing
`Pcf.IsWeightedNormalizedPCFDownstairs` predicate holds.

The actual scheme-point orbit and exact period two of `0` are proved in
the imported `BasilicaProjectiveScheme` module. All point and divisor
loci below concern actual schemes and the canonical normalization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.BasilicaProjectiveScheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
variable (k : Type*) [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "u" => (X (Sum.inl 0) : Coordinates k)
local notation "v" => (X (Sum.inr ()) : Coordinates k)

/-- The actual projective-line structure morphism over the ground field. -/
noncomputable def structureMap : Proj (grading k) ⟶ Spec (.of k) :=
  AlgebraicGeometry.Proj.toSpecZero (grading k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0)))

/-- Every actual standard projective chart has its usual polynomial structure map. -/
theorem anyTargetChart_comp_structureMap (e : Index ≃ Index) :
    Pcf.paperPAnyTargetChartToProj (K := k) e ≫ structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))) := by
  unfold Pcf.paperPAnyTargetChartToProj structureMap
  rw [Category.assoc, ← Category.assoc _ (AlgebraicGeometry.Proj.toSpecZero (grading k)) _,
    AlgebraicGeometry.Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change Pcf.paperPStandardChartDehomogenize
    (Pcf.paperPRenameAwayMap e (X (e.symm (Sum.inr ()))) v (by simp)
      (algebraMap (grading k 0) (Away (grading k) (X (e.symm (Sum.inr ()))))
        (algebraMap k (grading k 0) a))) = C a
  have ha : algebraMap (grading k 0) (Away (grading k) (X (e.symm (Sum.inr ()))))
      (algebraMap k (grading k 0) a) =
      Away.mk (grading k) (isHomogeneous_X k (e.symm (Sum.inr ()))) 0 (C a)
        (by exact isHomogeneous_C _ _) := rfl
  rw [ha, Pcf.paperPRenameAwayMap_mk]
  simp only [rename_C]
  rw [Pcf.paperPStandardChartDehomogenize_mk 0 (C a) (isHomogeneous_C _ a)]
  simp [Pcf.paperPDehomogenize]

instance structureMap_locallyOfFiniteType : LocallyOfFiniteType (structureMap k) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (Pcf.paperPProjectiveCoordinateOpenCover (K := k) (n := 1))).mpr
  intro b
  change LocallyOfFiniteType
    (Pcf.paperPAnyTargetChartToProj (Equiv.swap b (Sum.inr ())) ≫ structureMap k)
  rw [anyTargetChart_comp_structureMap]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The finite projective basilica morphism is surjective. -/
theorem global_schemeMap_surjective : Surjective (schemeMap k) := by
  rw [surjective_iff]
  intro p
  by_cases hp : v ∈ p.asHomogeneousIdeal
  · rw [(secondCoordinate_mem_iff k p).mp hp]
    exact ⟨infinity k, infinity_fixed k⟩
  · have hmem : p ∈ (affineEmbedding k).opensRange := by
      rw [affineEmbedding_opensRange]
      exact hp
    obtain ⟨q, rfl⟩ := hmem
    obtain ⟨r, hr⟩ := ((surjective_iff _).mp (BasilicaAffine.schemeMap_surjective k)) q
    refine ⟨affineEmbedding k r, ?_⟩
    have h := congrArg (fun f : Spec (.of (Polynomial k)) ⟶ Proj (grading k) => f r)
      (affineEmbedding_comp_map k)
    simpa only [Scheme.Hom.comp_apply, hr] using h

local instance finite : IsFinite (schemeMap k) := global_schemeMap_finite k
local instance surjective : Surjective (schemeMap k) := global_schemeMap_surjective k
local instance normalizationIso : IsIso (Pcf.Palomar.normalizationMap (Proj (grading k))) :=
  Pcf.normalScheme_normalizationMap_isIso _

/-- Normalized weighted critical divisor points lie in the actual non-étale locus. -/
theorem weightedCriticalPointSet_subset_nonEtale :
    Pcf.weightedCriticalPointSet (schemeMap k) ⊆ Pcf.schemeNonEtaleLocus (schemeMap k) := by
  rw [Pcf.weightedCriticalPointSet_eq_schemeDelta_of_normal]
  rintro p ⟨d, hd, rfl⟩
  change 1 < Pcf.schemeDivisorDelta (schemeMap k) d at hd
  change ¬ ((schemeMap k).stalkMap d.1).hom.FormallyEtale
  rw [← Pcf.schemeDivisorDelta_eq_one_iff_formallyEtale]
  omega

/-- Weighted postcritical divisor points lie in the actual non-étale point orbit. -/
theorem weightedPostcriticalPointSet_subset_globalNonEtalePostorbit :
    Pcf.weightedPostcriticalPointSet (schemeMap k) ⊆ globalNonEtalePostorbit k := by
  rw [Pcf.weightedPostcriticalPointSet, Pcf.weightedBranchPointSet_eq_image_criticalPointSet]
  intro y hy
  rcases Set.mem_iUnion.mp hy with ⟨n, q, ⟨p, hp, rfl⟩, rfl⟩
  refine ⟨p, weightedCriticalPointSet_subset_nonEtale k hp, n + 1,
    Nat.zero_lt_succ _, ?_⟩
  exact (Function.iterate_succ_apply (schemeMap k) n p).symm

/-- The actual projective basilica map satisfies the manuscript's normalized PCF predicate.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem isWeightedNormalizedPCF (h2 : (2 : k) ≠ 0) :
    Pcf.IsWeightedNormalizedPCFDownstairs k (structureMap k) (schemeMap k) := by
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    k (structureMap k) (schemeMap k)).mpr
  exact (globalNonEtalePostorbit_finite k h2).subset
    (weightedPostcriticalPointSet_subset_globalNonEtalePostorbit k)

/-- Coordinate swapping is a homeomorphism of the actual projective scheme points. -/
noncomputable def swapPointHomeomorph : Proj (grading k) ≃ₜ Proj (grading k) where
  toFun := swapPoint k
  invFun := swapPoint k
  left_inv := swapPoint_involutive k
  right_inv := swapPoint_involutive k
  continuous_toFun := (Pcf.paperPFormsProjectiveContinuousMap (swapForms k) 1
    Nat.zero_lt_one (swapForms_homogeneous k) (swapForms_cover k)).continuous
  continuous_invFun := (Pcf.paperPFormsProjectiveContinuousMap (swapForms k) 1
    Nat.zero_lt_one (swapForms_homogeneous k) (swapForms_cover k)).continuous

/-- The actual scheme origin has codimension one. -/
theorem zero_coheight : Order.coheight (zero k) = 1 := by
  have h := coheight_eq_of_isOpenImmersion
    (x := BasilicaAffine.closedPoint k 0) (affineEmbedding k)
  rw [affineEmbedding_closedPoint] at h
  change Order.coheight (zero k) = Order.coheight (BasilicaAffine.closedPoint k 0) at h
  rw [h, ← idealHeight_eq_coheight (.of (Polynomial k)) (BasilicaAffine.closedPoint k 0)]
  change (RingHom.ker (Polynomial.evalRingHom (0 : k))).height = 1
  rw [Polynomial.ker_evalRingHom]
  simp only [map_zero, sub_zero]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero) Polynomial.not_isUnit_X

/-- The actual scheme point at infinity has codimension one. -/
theorem infinity_coheight : Order.coheight (infinity k) = 1 := by
  have h := (swapPointHomeomorph k).isOpenEmbedding.coheight_eq (x := zero k)
  change Order.coheight (swapPoint k (zero k)) = Order.coheight (zero k) at h
  rw [swapPoint_zero, zero_coheight] at h
  exact h

/-- The actual codimension-one scheme point `0`. -/
noncomputable def zeroDivisor : Pcf.SchemeDivisorPoint (Proj (grading k)) :=
  ⟨zero k, zero_coheight k⟩
/-- The actual codimension-one scheme point `∞`. -/
noncomputable def infinityDivisor : Pcf.SchemeDivisorPoint (Proj (grading k)) :=
  ⟨infinity k, infinity_coheight k⟩

/-- A source divisor has weighted local degree greater than one exactly at `0` or `∞`. -/
theorem divisorDelta_gt_one_iff (h2 : (2 : k) ≠ 0)
    (d : Pcf.SchemeDivisorPoint (Proj (grading k))) :
    1 < Pcf.schemeDivisorDelta (schemeMap k) d ↔ d.1 = zero k ∨ d.1 = infinity k := by
  have hd : Pcf.schemeDivisorDelta (schemeMap k) d = 1 ↔
      Pcf.Stacks.IsStacksEtaleAt (schemeMap k) d.1 := by
    rw [Pcf.paperP_divisorDelta_eq_one_iff_etaleAt]
    constructor
    · rintro ⟨V, hV, U, hU, hUV, hp, he⟩
      exact ⟨U, hU, V, hV, hUV, hp, he⟩
    · rintro ⟨U, hU, V, hV, hUV, hp, he⟩
      exact ⟨V, hV, U, hU, hUV, hp, he⟩
  rw [global_etaleAt_iff k h2] at hd
  have hpos := Pcf.schemeDivisorDelta_pos_of_isFinite (schemeMap k) d
  constructor
  · intro h
    by_contra he
    have h1 := hd.mpr (not_or.mp he)
    omega
  · intro he
    have hn : Pcf.schemeDivisorDelta (schemeMap k) d ≠ 1 := by
      intro h1
      exact (not_or.mpr (hd.mp h1)) he
    omega

/-- The canonical-normalization critical generic-point set is exactly `{0, ∞}`. -/
theorem weightedCriticalPointSet_eq_pair (h2 : (2 : k) ≠ 0) :
    Pcf.weightedCriticalPointSet (schemeMap k) = {zero k, infinity k} := by
  rw [Pcf.weightedCriticalPointSet_eq_schemeDelta_of_normal]
  ext p
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (divisorDelta_gt_one_iff k h2 d).mp hd
  · rintro (rfl | hp)
    · exact ⟨zeroDivisor k, (divisorDelta_gt_one_iff k h2 _).mpr (Or.inl rfl), rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hp
      exact ⟨infinityDivisor k, (divisorDelta_gt_one_iff k h2 _).mpr (Or.inr rfl), rfl⟩

/-- The canonical-normalization branch generic-point set is exactly `{-1, ∞}`. -/
theorem weightedBranchPointSet_eq_pair (h2 : (2 : k) ≠ 0) :
    Pcf.weightedBranchPointSet (schemeMap k) = {minusOne k, infinity k} := by
  rw [Pcf.weightedBranchPointSet_eq_image_criticalPointSet, weightedCriticalPointSet_eq_pair k h2,
    Set.image_pair, zero_to_minusOne, infinity_fixed]

/-- The normalized weighted postcritical generic-point set is exactly `{0, -1, ∞}`.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem weightedPostcriticalPointSet_eq_threePoints (h2 : (2 : k) ≠ 0) :
    Pcf.weightedPostcriticalPointSet (schemeMap k) = threePoints k := by
  apply Set.Subset.antisymm
  · rw [← globalNonEtalePostorbit_eq_threePoints k h2]
    exact weightedPostcriticalPointSet_subset_globalNonEtalePostorbit k
  · intro p hp
    rw [Pcf.weightedPostcriticalPointSet, weightedBranchPointSet_eq_pair k h2]
    rcases hp with rfl | hp
    · exact Set.mem_iUnion.mpr ⟨1, minusOne k, by simp, minusOne_to_zero k⟩
    rcases hp with rfl | hp
    · exact Set.mem_iUnion.mpr ⟨0, minusOne k, by simp, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact Set.mem_iUnion.mpr ⟨0, infinity k, by simp, rfl⟩

/-- The finite-type clause of Stacks Lemma 33.34.1 for the actual projective line.

Divergence from Stacks: this states only finite type over the field, as
local finite type and quasi-compactness; smoothness, projectivity and the
full variety assertion are not part of this declaration. -/
@[stacks 0B2P "finite-type part of the variety assertion, projective line"]
theorem structureMap_finiteType :
    LocallyOfFiniteType (structureMap k) ∧ QuasiCompact (structureMap k) :=
  ⟨inferInstance, inferInstance⟩

theorem zero_isClosed : IsClosed ({zero k} : Set (Proj (grading k))) := by
  have he : ({zero k} : Set (Proj (grading k))) =
      ProjectiveSpectrum.zeroLocus (grading k) {u} := by
    ext p
    change p = zero k ↔ ({u} : Set (Coordinates k)) ⊆ (p.asHomogeneousIdeal : Set _)
    rw [Set.singleton_subset_iff]
    exact (firstCoordinate_mem_iff k p).symm
  rw [he]
  exact ProjectiveSpectrum.isClosed_zeroLocus _ _

theorem infinity_isClosed : IsClosed ({infinity k} : Set (Proj (grading k))) := by
  have h := (swapPointHomeomorph k).isClosedMap _ (zero_isClosed k)
  change IsClosed (swapPoint k '' {zero k}) at h
  simpa only [Set.image_singleton, swapPoint_zero] using h

theorem minusOne_isClosed : IsClosed ({minusOne k} : Set (Proj (grading k))) := by
  have h := (schemeMap k).isClosedMap _ (zero_isClosed k)
  simpa only [Set.image_singleton, zero_to_minusOne] using h

/-- The manuscript's closed normalized weighted critical locus is exactly `{0, ∞}`.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem weightedCriticalLocus_eq_pair (h2 : (2 : k) ≠ 0) :
    Pcf.weightedCriticalLocus (schemeMap k) = {zero k, infinity k} := by
  have hc : IsClosed ({zero k, infinity k} : Set (Proj (grading k))) :=
    (zero_isClosed k).union (infinity_isClosed k)
  rw [Pcf.weightedCriticalLocus, weightedCriticalPointSet_eq_pair k h2, hc.closure_eq]

/-- The manuscript's closed normalized weighted branch locus is exactly `{-1, ∞}`.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem weightedBranchLocus_eq_pair (h2 : (2 : k) ≠ 0) :
    Pcf.weightedBranchLocus (schemeMap k) = {minusOne k, infinity k} := by
  have hc : IsClosed ({minusOne k, infinity k} : Set (Proj (grading k))) :=
    (minusOne_isClosed k).union (infinity_isClosed k)
  rw [Pcf.weightedBranchLocus, weightedBranchPointSet_eq_pair k h2, hc.closure_eq]

/-- The actual function-field extension of the basilica map is separable. -/
theorem isGenericallySeparable (h2 : (2 : k) ≠ 0) :
    Pcf.IsGenericallySeparable (schemeMap k) := by
  apply Pcf.isGenericallySeparable_of_formallyEtale_generic
  apply (Pcf.paperPFormsProjective_stalk_formallyEtale_iff (forms k) 2 (by decide)
    (forms_homogeneous k) (forms_cover k) h2 _).mpr
  rw [jacobian_mem_iff k h2]
  apply not_or.mpr
  have h0 : Order.coheight (genericPoint (Proj (grading k))) = 0 := by
    change Order.coheight (⊤ : Proj (grading k)) = 0
    exact Order.coheight_top _
  constructor
  · intro he
    rw [he, zero_coheight] at h0
    norm_num at h0
  · intro he
    rw [he, infinity_coheight] at h0
    norm_num at h0

/-- The actual polynomial chart embedding is a morphism over the ground field. -/
theorem affineEmbedding_comp_structureMap :
    affineEmbedding k ≫ structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  unfold affineEmbedding affineEmbeddingMv structureMap
  simp only [Category.assoc]
  rw [← Category.assoc _ (AlgebraicGeometry.Proj.toSpecZero (grading k)) _,
    AlgebraicGeometry.Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change MvPolynomial.uniqueAlgEquiv k (Fin 1)
    (Pcf.paperPStandardChartDehomogenize
      (algebraMap (grading k 0) (Away (grading k) v)
        (algebraMap k (grading k 0) a))) = Polynomial.C a
  have ha : algebraMap (grading k 0) (Away (grading k) v)
      (algebraMap k (grading k 0) a) =
      Away.mk (grading k) (isHomogeneous_X k (Sum.inr ())) 0 (C a)
        (by exact isHomogeneous_C _ _) := rfl
  rw [ha, Pcf.paperPStandardChartDehomogenize_mk 0 (C a) (isHomogeneous_C _ a)]
  simp [Pcf.paperPDehomogenize]

/-- The actual global basilica scheme morphism is defined over the ground field. -/
theorem schemeMap_comp_structureMap : schemeMap k ≫ structureMap k = structureMap k := by
  haveI : IsDominant (affineEmbedding k) :=
    ⟨(affineEmbedding k).isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  apply AlgebraicGeometry.ext_of_isDominant (affineEmbedding k)
  rw [← Category.assoc, affineEmbedding_comp_map, Category.assoc,
    affineEmbedding_comp_structureMap]
  unfold BasilicaAffine.schemeMap
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (BasilicaAffine.coordinateMap k).commutes a

/-- In the source example's characteristic-zero scope, basilica is PCF all the way down.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem isPCFAllSubvarieties [CharZero k] :
    Pcf.IsPCFAllSubvarieties k (structureMap k) (schemeMap k) :=
  Pcf.isPCFAllSubvarieties_charZero_of_downstairsPCF k (structureMap k) (schemeMap k)
    (isWeightedNormalizedPCF k (by norm_num))

end Pcf.Examples.PaperP.BasilicaProjectiveScheme
