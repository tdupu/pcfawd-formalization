/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaProjectiveScheme
public import Pcf.Examples.PaperP.BasilicaAffineEtale
public import Pcf.Bounding.PaperPJacobianStandardChart
/-!
# The actual affine chart of the global basilica scheme map

For `latex/paper-p.tex`, Example `ex:basilica`, this module identifies the
restriction of the global Proj morphism to its standard affine open with
the proved affine basilica scheme map. It proves the commuting square,
finiteness of that actual restriction, and the full pointwise étale
criterion on this projective open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
open AlgebraicGeometry.ProjectiveSpectrum
namespace Pcf.Examples.PaperP.BasilicaProjectiveScheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
variable (k : Type*) [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "lastX" => (X (Sum.inr ()) : Coordinates k)
noncomputable def affineOpen : (Proj (grading k)).Opens := AlgebraicGeometry.Proj.basicOpen (grading k) lastX
/-- The homogeneous chart pullback with both denominators the last coordinate. -/
noncomputable def standardPullback : Away (grading k) lastX →+* Away (grading k) lastX :=
  Pcf.paperPDegreeLocalizationMap (𝒜 := grading k) (ℬ := grading k)
    (aeval (forms k)).toRingHom 2 (Pcf.paperPForms_degreeMap (forms k) 2 (forms_homogeneous k))
    (by
      rintro p ⟨m, rfl⟩
      change aeval (forms k) (lastX ^ m) ∈ Submonoid.powers lastX
      simp only [map_pow, aeval_X, forms]
      exact ⟨2 * m, pow_mul _ _ _⟩)

theorem standard_awayToSection_comp_appLE :
    AlgebraicGeometry.Proj.awayToSection (grading k) lastX ≫
      (schemeMap k).appLE (affineOpen k) (affineOpen k)
        (by rw [affineOpen, preimage_affineChart]) =
      CommRingCat.ofHom (standardPullback k) ≫ AlgebraicGeometry.Proj.awayToSection (grading k) lastX := by
  ext z
  obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective (grading k) (isHomogeneous_X k (Sum.inr ())) z
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  refine Subtype.ext <| funext fun p => ?_
  change HomogeneousLocalization.mk _ = HomogeneousLocalization.mk _
  ext
  simp [Pcf.paperPDegreeMapFraction, forms]

/-- The homogeneous standard chart inclusion commutes with the global map. -/
theorem standard_awayι_comp_map :
    AlgebraicGeometry.Proj.awayι (grading k) lastX (isHomogeneous_X k (Sum.inr ())) Nat.zero_lt_one ≫
      schemeMap k = Spec.map (CommRingCat.ofHom (standardPullback k)) ≫
        AlgebraicGeometry.Proj.awayι (grading k) lastX (isHomogeneous_X k (Sum.inr ())) Nat.zero_lt_one := by
  have hι : (affineOpen k).ι ≫ schemeMap k =
      (schemeMap k).resLE (affineOpen k) (affineOpen k)
        (by rw [affineOpen, preimage_affineChart]) ≫ (affineOpen k).ι := by simp
  dsimp only [affineOpen] at hι
  rw [AlgebraicGeometry.Proj.awayι, Category.assoc, hι, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine AlgebraicGeometry.ext_to_Spec <|
    (cancel_mono (affineOpen k).topIso.hom).mp ?_
  simp [AlgebraicGeometry.Proj.basicOpenIsoSpec_hom, AlgebraicGeometry.Proj.basicOpenToSpec_app_top]
  simpa only [affineOpen] using standard_awayToSection_comp_appLE k
noncomputable def affineCoordinateMap :
    MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 1) k :=
  aeval (fun _ => X 0 ^ 2 - 1)

theorem dehomogenize_comp_forms :
    Pcf.paperPDehomogenize.comp (aeval (forms k)) =
      (affineCoordinateMap k).comp Pcf.paperPDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [forms, affineCoordinateMap, Pcf.paperPDehomogenize]

theorem standardPullback_mk (m : ℕ) (P : Coordinates k)
    (hP : P ∈ grading k m) :
    (standardPullback k)
        (Away.mk (grading k) (isHomogeneous_X k (Sum.inr ())) m P (by simpa only [smul_eq_mul, mul_one] using hP)) =
      Away.mk (grading k) (isHomogeneous_X k (Sum.inr ())) (2 * m)
        (aeval (forms k) P) (by
          simpa only [smul_eq_mul, mul_one] using
            (Pcf.paperPForms_degreeMap (forms k) 2 (forms_homogeneous k) m P hP)) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (aeval (forms k) P) ⟨aeval (forms k) (lastX ^ m), _⟩ =
    Localization.mk (aeval (forms k) P) ⟨lastX ^ (2 * m), _⟩
  congr 1
  ext
  simp [forms, pow_mul]

/-- Dehomogenization identifies the chart pullback with `t ↦ t²-1`. -/
theorem standardPullback_dehomogenize (z : Away (grading k) lastX) :
    Pcf.paperPStandardChartRingEquiv (K := k) (n := 1) (standardPullback k z) =
      affineCoordinateMap k (Pcf.paperPStandardChartRingEquiv (K := k) (n := 1) z) := by
  obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective (grading k) (isHomogeneous_X k (Sum.inr ())) z
  have hP' : P ∈ grading k m := by simpa only [smul_eq_mul, mul_one] using hP
  rw [standardPullback_mk k m P hP']
  change Pcf.paperPStandardChartDehomogenize _ =
    affineCoordinateMap k (Pcf.paperPStandardChartDehomogenize _)
  rw [Pcf.paperPStandardChartDehomogenize_mk (2 * m) (aeval (forms k) P)
      (Pcf.paperPForms_degreeMap (forms k) 2 (forms_homogeneous k) m P hP'),
    Pcf.paperPStandardChartDehomogenize_mk m P hP']
  exact congrArg (fun f : Coordinates k →ₐ[k] MvPolynomial (Fin 1) k => f P)
    (dehomogenize_comp_forms k)
noncomputable def affineEmbeddingMv :
    Spec (.of (MvPolynomial (Fin 1) k)) ⟶ Proj (grading k) :=
  Spec.map (CommRingCat.ofHom
    (Pcf.paperPStandardChartRingEquiv (K := k) (n := 1)).toRingHom) ≫
      AlgebraicGeometry.Proj.awayι (grading k) lastX
        (isHomogeneous_X k (Sum.inr ())) Nat.zero_lt_one

theorem affineEmbeddingMv_comp_map :
    affineEmbeddingMv k ≫ schemeMap k =
      Spec.map (CommRingCat.ofHom (affineCoordinateMap k).toRingHom) ≫ affineEmbeddingMv k := by
  unfold affineEmbeddingMv
  rw [Category.assoc, standard_awayι_comp_map, ← Category.assoc, ← Spec.map_comp]
  rw [← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun q : CommRingCat.of (Away (grading k) lastX) ⟶
      CommRingCat.of (MvPolynomial (Fin 1) k) => Spec.map q ≫
        AlgebraicGeometry.Proj.awayι (grading k) lastX
          (isHomogeneous_X k (Sum.inr ())) Nat.zero_lt_one)
  apply CommRingCat.hom_ext
  exact RingHom.ext (standardPullback_dehomogenize k)

theorem affineCoordinateMap_conjugate :
    (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toAlgHom.comp (affineCoordinateMap k) =
      (BasilicaAffine.coordinateMap k).comp (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [affineCoordinateMap, BasilicaAffine.coordinateMap,
    MvPolynomial.uniqueAlgEquiv_apply]

/-- The ordinary polynomial affine line as the standard projective open. -/
noncomputable def affineEmbedding : Spec (.of (Polynomial k)) ⟶ Proj (grading k) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toRingHom) ≫
    affineEmbeddingMv k

/-- The actual global basilica morphism restricts to the actual affine morphism.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem affineEmbedding_comp_map :
    affineEmbedding k ≫ schemeMap k = BasilicaAffine.schemeMap k ≫ affineEmbedding k := by
  unfold affineEmbedding
  rw [Category.assoc, affineEmbeddingMv_comp_map, ← Category.assoc, ← Spec.map_comp]
  unfold BasilicaAffine.schemeMap
  rw [← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun q : CommRingCat.of (MvPolynomial (Fin 1) k) ⟶
      CommRingCat.of (Polynomial k) => Spec.map q ≫ affineEmbeddingMv k)
  exact congrArg (fun f : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k => CommRingCat.ofHom f.toRingHom)
    (affineCoordinateMap_conjugate k)
instance affineEmbeddingMv_isOpenImmersion : IsOpenImmersion (affineEmbeddingMv k) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (Pcf.paperPStandardChartRingEquiv (K := k) (n := 1)).toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso
      (Pcf.paperPStandardChartRingEquiv (K := k) (n := 1)).toCommRingCatIso.op).hom
    infer_instance
  unfold affineEmbeddingMv
  infer_instance

instance affineEmbedding_isOpenImmersion : IsOpenImmersion (affineEmbedding k) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso
      (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toCommRingCatIso.op).hom
    infer_instance
  unfold affineEmbedding
  infer_instance

/-- The standard projective open is the ordinary affine line. -/
noncomputable def affineChartIso : (affineOpen k).toScheme ≅ Spec (.of (Polynomial k)) :=
  Pcf.paperPStandardChartSchemeIso (K := k) (n := 1) ≪≫
    (Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toCommRingCatIso.op).symm

theorem affineChartIso_inv_comp_ι :
    (affineChartIso k).inv ≫ (affineOpen k).ι = affineEmbedding k := by
  simp [affineChartIso, Pcf.paperPStandardChartSchemeIso, affineEmbedding,
    affineEmbeddingMv, AlgebraicGeometry.Proj.awayι, Category.assoc, affineOpen, grading]

noncomputable def affineRestriction : (affineOpen k).toScheme ⟶ (affineOpen k).toScheme :=
  (schemeMap k).resLE (affineOpen k) (affineOpen k)
    (by rw [affineOpen, preimage_affineChart])

/-- The actual open restriction is conjugate to the actual affine basilica map. -/
theorem affineRestriction_eq_conjugate :
    affineRestriction k = (affineChartIso k).hom ≫ BasilicaAffine.schemeMap k ≫
      (affineChartIso k).inv := by
  have h := affineEmbedding_comp_map k
  rw [← affineChartIso_inv_comp_ι] at h
  have hres : (affineOpen k).ι ≫ schemeMap k = affineRestriction k ≫ (affineOpen k).ι := by
    simp [affineRestriction]
  simp only [Category.assoc] at h
  rw [hres, ← Category.assoc, ← Category.assoc] at h
  have h' := (cancel_mono (affineOpen k).ι).mp h
  apply (cancel_epi (affineChartIso k).inv).mp
  simpa [Category.assoc] using h'

/-- The actual restriction over the standard target open is finite. -/
theorem affineRestriction_finite : IsFinite (affineRestriction k) := by
  rw [affineRestriction_eq_conjugate]
  letI : IsFinite (BasilicaAffine.schemeMap k) := BasilicaAffine.schemeMap_finite k
  infer_instance

theorem affineEmbedding_opensRange : (affineEmbedding k).opensRange = affineOpen k := by
  have h := Scheme.Hom.opensRange_comp_of_isIso (affineChartIso k).inv (affineOpen k).ι
  simpa only [affineChartIso_inv_comp_ι, Scheme.Opens.opensRange_ι] using h

/-- Pointwise étaleness is unchanged by postcomposition with an open immersion.

Divergence from Stacks: this is the pointwise open-immersion case of the
cancellation statement in Tag `0HB1`. The converse uses composition, Tag
`02GN`, and the fact that an open immersion is étale. The global source
statements are applied on the étale source neighbourhood in each direction.
-/
@[stacks 0HB1 "pointwise cancellation, postcomposition with an open immersion",
  stacks 02GN "pointwise composition, postcomposition with an open immersion"]
private theorem etaleAt_postcomp_open_iff {X Y Z : Scheme} (f : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion i] (x : X) :
    Pcf.Stacks.IsStacksEtaleAt (f ≫ i) x ↔ Pcf.Stacks.IsStacksEtaleAt f x := by
  rw [Pcf.Stacks.isStacksEtaleAt_iff_exists_etale,
    Pcf.Stacks.isStacksEtaleAt_iff_exists_etale]
  constructor
  · rintro ⟨U, hx, he⟩
    refine ⟨U, hx, ?_⟩
    haveI : Etale ((U.ι ≫ f) ≫ i) := by simpa [Category.assoc] using he
    exact Etale.of_comp (U.ι ≫ f) i
  · rintro ⟨U, hx, he⟩
    refine ⟨U, hx, ?_⟩
    haveI : Etale (U.ι ≫ f) := he
    simpa [Category.assoc] using (inferInstance : Etale ((U.ι ≫ f) ≫ i))

theorem global_etaleAt_affineEmbedding_iff (p : Spec (.of (Polynomial k))) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k) (affineEmbedding k p) ↔
      Pcf.Stacks.IsStacksEtaleAt (BasilicaAffine.schemeMap k) p := by
  have hc := Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
    (f := schemeMap k) (affineEmbedding k) p
  rw [affineEmbedding_comp_map] at hc
  exact hc.symm.trans (etaleAt_postcomp_open_iff _ _ _)

/-- The global morphism is étale on its affine chart exactly away from the origin.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem global_etaleAt_affine_iff_ne_zero [CharZero k] (p : Spec (.of (Polynomial k))) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k) (affineEmbedding k p) ↔
      p ≠ BasilicaAffine.closedPoint k 0 := by
  rw [global_etaleAt_affineEmbedding_iff, BasilicaAffine.etaleAt_iff_ne_zero]

#print axioms affineEmbedding_comp_map
#print axioms affineEmbedding_isOpenImmersion
#print axioms affineEmbedding_opensRange
#print axioms affineRestriction_eq_conjugate
#print axioms affineRestriction_finite
#print axioms etaleAt_postcomp_open_iff
#print axioms global_etaleAt_affine_iff_ne_zero

end Pcf.Examples.PaperP.BasilicaProjectiveScheme
