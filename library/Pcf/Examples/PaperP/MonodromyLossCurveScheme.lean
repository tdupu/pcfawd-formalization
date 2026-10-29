/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossCurveGlue
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Global properties of the glued curve `E` of `ex:monodromy-loss`

For `latex/paper-p.tex`, Example `ex:monodromy-loss` (Part II), with `E` the two-chart
gluing of `MonodromyLossCurveGlue`:

* `isPullback_charts`: the overlap square `Spec A[1/y] ⇉ Spec A, Spec B ⟶ E` is a pullback;
* `desc`, `hom_ext`: morphisms out of `E` from compatible chart morphisms;
* `toSpec : E ⟶ Spec k`, `LocallyOfFiniteType`, `QuasiCompact` (finite type);
* `B_isDomain` (Eisenstein at `(w)`), `isIntegral` (`E` integral);
* `toSpec_isSeparated` (diagonal is a closed immersion, checked on the four affine pieces
  `U_a ×_k U_b`; for `a ≠ b` via surjectivity of `A ⊗_k B → A[1/y]`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u
variable (k : Type u) [Field k]

/-- `Spec A[1/y] ⟶ Spec A`. -/
noncomputable def jA : Spec (.of (Ay k)) ⟶ Spec (.of (A k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ay k)))
/-- `Spec A[1/y] ⟶ Spec B`, `s ↦ x/y`, `w ↦ 1/y`. -/
noncomputable def jB : Spec (.of (Ay k)) ⟶ Spec (.of (B k)) :=
  Spec.map (CommRingCat.ofHom (BtoAy k))

theorem BwToAy_comp_algebraMap : (BwToAy k).comp (algebraMap (B k) (Bw k)) = BtoAy k :=
  RingHom.ext fun b => BwToAy_algebraMap k b

theorem isPullback_charts : IsPullback (jA k) (jB k) (ιA k) (ιB k) := by
  have hV := IsPullback.of_isLimit ((glueData k).vPullbackConeIsLimit ⟨false⟩ ⟨true⟩)
  have hne : (⟨false⟩ : Idx.{u}) ≠ ⟨true⟩ := by simp
  refine IsPullback.of_iso hV (eqToIso (dite_eq_right hne)) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Scheme.GlueData.vPullbackCone, glueData, GlueData.ofGlueData', hne, glueData',
      GlueData'.f', overlapι, jA]
  · simp [Scheme.GlueData.vPullbackCone, glueData, GlueData.ofGlueData', hne, glueData',
      GlueData'.f', hne.symm, overlapι, transition, jB, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      BwToAy_comp_algebraMap]
  · simp [ιA]
  · simp [ιB]


/-- The two chart morphisms, indexed. -/
noncomputable def chartFamily {Y : Scheme.{u}} (gA : Spec (.of (A k)) ⟶ Y)
    (gB : Spec (.of (B k)) ⟶ Y) : ∀ i : Idx.{u}, (glueData k).openCover.X i ⟶ Y
  | ⟨false⟩ => gA
  | ⟨true⟩ => gB

/-- **Morphisms out of `E`** from compatible chart morphisms. -/
noncomputable def desc {Y : Scheme.{u}} (gA : Spec (.of (A k)) ⟶ Y)
    (gB : Spec (.of (B k)) ⟶ Y) (h : jA k ≫ gA = jB k ≫ gB) : E k ⟶ Y :=
  (glueData k).openCover.glueMorphisms (chartFamily k gA gB) (by
    have hP := isPullback_charts k
    rintro ⟨_ | _⟩ ⟨_ | _⟩
    · rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst (ιA k) (ιB k) ≫ gA = pullback.snd (ιA k) (ιB k) ≫ gB
      rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc, h]
    · change pullback.fst (ιB k) (ιA k) ≫ gB = pullback.snd (ιB k) (ιA k) ≫ gA
      rw [← cancel_epi hP.flip.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc, h]
    · rw [fst_eq_snd_of_mono_eq])

@[simp]
theorem ιA_desc {Y : Scheme.{u}} (gA : Spec (.of (A k)) ⟶ Y)
    (gB : Spec (.of (B k)) ⟶ Y) (h : jA k ≫ gA = jB k ≫ gB) : ιA k ≫ desc k gA gB h = gA :=
by
  unfold desc
  exact (glueData k).openCover.ι_glueMorphisms (chartFamily k gA gB) _ ⟨false⟩

@[simp]
theorem ιB_desc {Y : Scheme.{u}} (gA : Spec (.of (A k)) ⟶ Y)
    (gB : Spec (.of (B k)) ⟶ Y) (h : jA k ≫ gA = jB k ≫ gB) : ιB k ≫ desc k gA gB h = gB :=
by
  unfold desc
  exact (glueData k).openCover.ι_glueMorphisms (chartFamily k gA gB) _ ⟨true⟩

theorem hom_ext {Y : Scheme.{u}} {g₁ g₂ : E k ⟶ Y} (hA : ιA k ≫ g₁ = ιA k ≫ g₂)
    (hB : ιB k ≫ g₁ = ιB k ≫ g₂) : g₁ = g₂ :=
  (glueData k).openCover.hom_ext _ _ (by rintro ⟨_ | _⟩; exacts [hA, hB])

theorem BtoAy_comp_algebraMap : (BtoAy k).comp (algebraMap k (B k)) = algebraMap k (Ay k) :=
  RingHom.ext fun a => by simp only [RingHom.comp_apply, BtoAy, liftB_algebraMap]

theorem algebraMap_A_Ay_comp : (algebraMap (A k) (Ay k)).comp (algebraMap k (A k)) =
    algebraMap k (Ay k) :=
  (IsScalarTower.algebraMap_eq k (A k) (Ay k)).symm

set_option backward.isDefEq.respectTransparency true in
theorem toSpec_compat : jA k ≫ Spec.map (CommRingCat.ofHom (algebraMap k (A k))) =
    jB k ≫ Spec.map (CommRingCat.ofHom (algebraMap k (B k))) := by
  have h : CommRingCat.ofHom (algebraMap k (A k)) ≫ CommRingCat.ofHom (algebraMap (A k) (Ay k)) =
      CommRingCat.ofHom (algebraMap k (B k)) ≫ CommRingCat.ofHom (BtoAy k) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, BtoAy_comp_algebraMap,
      algebraMap_A_Ay_comp]
  unfold jA jB
  rw [← Spec.map_comp, ← Spec.map_comp, h]

/-- The structure morphism `E ⟶ Spec k`. -/
noncomputable def toSpec : E k ⟶ Spec (.of k) :=
  desc k (Spec.map (CommRingCat.ofHom (algebraMap k (A k))))
    (Spec.map (CommRingCat.ofHom (algebraMap k (B k)))) (toSpec_compat k)

@[simp]
theorem ιA_toSpec : ιA k ≫ toSpec k = Spec.map (CommRingCat.ofHom (algebraMap k (A k))) :=
  ιA_desc k _ _ _

@[simp]
theorem ιB_toSpec : ιB k ≫ toSpec k = Spec.map (CommRingCat.ofHom (algebraMap k (B k))) :=
  ιB_desc k _ _ _

instance : Algebra.FiniteType k (A k) := inferInstance
instance : Algebra.FiniteType k (B k) := inferInstance

/-- **Step (1).** `E ⟶ Spec k` is locally of finite type. -/
instance toSpec_locallyOfFiniteType : LocallyOfFiniteType (toSpec k) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) (glueData k).openCover]
  rintro ⟨_ | _⟩
  · change LocallyOfFiniteType (ιA k ≫ toSpec k)
    rw [ιA_toSpec, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · change LocallyOfFiniteType (ιB k ≫ toSpec k)
    rw [ιB_toSpec, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- `E` is quasi-compact (two affine charts). -/
instance compactSpace : CompactSpace (E k) := by
  constructor
  have : (Set.univ : Set (E k)) = Set.range (ιA k) ∪ Set.range (ιB k) := by
    ext x; simpa using chart_cover k x
  rw [this]
  exact (isCompact_range (ιA k).continuous).union (isCompact_range (ιB k).continuous)

/-- **Step (4).** `E ⟶ Spec k` is quasi-compact (hence of finite type with step (1)). -/
instance toSpec_quasiCompact : QuasiCompact (toSpec k) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr (compactSpace k)

/-! ### Integrality -/

theorem fB_coeff_zero : (fB k).coeff 0 = -X := by
  simp only [fB, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]; simp
theorem fB_coeff_one : (fB k).coeff 1 = -X ^ 2 := by
  simp only [fB, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]; simp
theorem fB_coeff_two : (fB k).coeff 2 = 0 := by
  simp only [fB, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]; simp

theorem fB_natDegree : (fB k).natDegree = 3 := by
  unfold fB; compute_degree!

theorem fB_monic : (fB k).Monic := by
  unfold fB; monicity!

theorem fB_isEisensteinAt : (fB k).IsEisensteinAt (Ideal.span {(X : k[X])}) where
  leading := by
    rw [(fB_monic k).leadingCoeff]
    intro h
    exact (Ideal.span_singleton_prime (Polynomial.X_ne_zero) |>.mpr Polynomial.prime_X).ne_top
      ((Ideal.eq_top_iff_one _).mpr h)
  mem {n} hn := by
    rw [fB_natDegree] at hn
    interval_cases n
    · rw [fB_coeff_zero]; exact neg_mem (Ideal.subset_span rfl)
    · rw [fB_coeff_one, pow_two]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    · rw [fB_coeff_two]; exact zero_mem _
  notMem := by
    rw [fB_coeff_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_neg,
      Polynomial.X_pow_dvd_iff]
    intro h
    simpa using h 1 (by norm_num)

theorem fB_irreducible : Irreducible (fB k) :=
  (fB_isEisensteinAt k).irreducible
    ((Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X)
    (fB_monic k).isPrimitive (by rw [fB_natDegree]; norm_num)

instance B_isDomain : IsDomain (B k) :=
  AdjoinRoot.isDomain_of_prime (fB_irreducible k).prime


theorem yA_ne_zero : yA k ≠ 0 := by
  have h := (WeierstrassCurve.Affine.CoordinateRing.basis (W k)).ne_zero 1
  rwa [WeierstrassCurve.Affine.CoordinateRing.basis_one] at h

instance Ay_nontrivial : Nontrivial (Ay k) :=
  (IsLocalization.injective (Ay k)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (yA_ne_zero k))).nontrivial

/-- The two charts of `E` meet. -/
theorem range_ιA_inter_range_ιB_nonempty :
    (Set.range (ιA k) ∩ Set.range (ιB k)).Nonempty := by
  obtain ⟨p⟩ : Nonempty (Spec (.of (Ay k))) := inferInstanceAs (Nonempty (PrimeSpectrum (Ay k)))
  refine ⟨ιA k (jA k p), ⟨_, rfl⟩, ⟨jB k p, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (isPullback_charts k).w]

instance irreducibleSpace : IrreducibleSpace (E k) := by
  have hU : IsIrreducible (Set.range (ιA k)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (ιA k).continuous.continuousOn
  have hV : IsIrreducible (Set.range (ιB k)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (ιB k).continuous.continuousOn
  have hcl : closure (Set.range (ιA k)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases chart_cover k x with hx | hx
    · exact subset_closure hx
    · have := subset_closure_inter_of_isPreirreducible_of_isOpen hV.2
        (ιA k).isOpenEmbedding.isOpen_range
        (by rw [Set.inter_comm]; exact range_ιA_inter_range_ιB_nonempty k) hx
      exact closure_mono Set.inter_subset_right this
  rw [irreducibleSpace_def]
  simpa [hcl] using hU.closure

instance isReduced : IsReduced (E k) := by
  have : ∀ i, IsReduced ((glueData k).openCover.X i) := by
    rintro ⟨_ | _⟩
    · change IsReduced (Spec (.of (A k))); infer_instance
    · change IsReduced (Spec (.of (B k))); infer_instance
  exact IsReduced.of_openCover (X := E k) (glueData k).openCover

/-- **Step (2).** `E` is an integral scheme. -/
instance isIntegral : IsIntegral (E k) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-! ### Separatedness -/

section Separated
variable {k}

open TensorProduct Algebra.TensorProduct in
/-- An affine piece of the diagonal: if two affine opens `Spec R₁, Spec R₂` of `X/Spec k`
meet in `Spec C` (a pullback square of `Spec` of `k`-algebra maps), and
`R₁ ⊗_k R₂ → C` is surjective, then `U₁ ×_X U₂ ⟶ U₁ ×_k U₂` is a closed immersion. -/
theorem isClosedImmersion_pullback_map_of_affine {k : Type u} [Field k] {X : Scheme.{u}}
    (str : X ⟶ Spec (.of k)) {R₁ R₂ C : Type u} [CommRing R₁] [CommRing R₂] [CommRing C]
    [Algebra k R₁] [Algebra k R₂] [Algebra k C] (u₁ : Spec (.of R₁) ⟶ X)
    (u₂ : Spec (.of R₂) ⟶ X) (hu₁ : u₁ ≫ str = Spec.map (CommRingCat.ofHom (algebraMap k R₁)))
    (hu₂ : u₂ ≫ str = Spec.map (CommRingCat.ofHom (algebraMap k R₂)))
    (ψ₁ : R₁ →ₐ[k] C) (ψ₂ : R₂ →ₐ[k] C)
    (hP : IsPullback (Spec.map (CommRingCat.ofHom ψ₁.toRingHom))
      (Spec.map (CommRingCat.ofHom ψ₂.toRingHom)) u₁ u₂)
    (hsurj : Function.Surjective (productMap ψ₁ ψ₂)) :
    IsClosedImmersion (pullback.map u₁ u₂ (u₁ ≫ str) (u₂ ≫ str) (𝟙 _) (𝟙 _) str
      (by simp) (by simp)) := by
  let e : pullback (u₁ ≫ str) (u₂ ≫ str) ≅ Spec (.of (R₁ ⊗[k] R₂)) :=
    pullback.congrHom hu₁ hu₂ ≪≫ pullbackSpecIso k R₁ R₂
  have key : hP.isoPullback.hom ≫ pullback.map u₁ u₂ (u₁ ≫ str) (u₂ ≫ str) (𝟙 _) (𝟙 _) str
      (by simp) (by simp) =
      Spec.map (CommRingCat.ofHom (productMap ψ₁ ψ₂).toRingHom) ≫ e.inv := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id,
        IsPullback.isoPullback_hom_fst,
        e, Iso.trans_inv, pullback.congrHom_inv]
      rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1; ext a; simp
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id,
        IsPullback.isoPullback_hom_snd,
        e, Iso.trans_inv, pullback.congrHom_inv]
      rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1; ext a; simp
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (productMap ψ₁ ψ₂).toRingHom) ≫ e.inv) :=
    have := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (productMap ψ₁ ψ₂).toRingHom) hsurj
    inferInstance
  rw [← key] at this
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mp this

variable (k)

/-- `B → A[1/y]` as a `k`-algebra map. -/
noncomputable def BtoAyₐ : B k →ₐ[k] Ay k :=
  { BtoAy k with commutes' := fun a => liftB_algebraMap k _ _ _ a }

open Algebra.TensorProduct in
theorem productMap_AB_surjective :
    Function.Surjective (productMap (IsScalarTower.toAlgHom k (A k) (Ay k)) (BtoAyₐ k)) := by
  intro z
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (yA k) z
  refine ⟨a ⊗ₜ (wB k ^ n), ?_⟩
  have hw : BtoAyₐ k (wB k) = invY k := by
    change BtoAy k (wB k) = _; rw [BtoAy, liftB_w]
  rw [productMap_apply_tmul, map_pow, hw, IsScalarTower.coe_toAlgHom', ← h, mul_assoc,
    ← mul_pow, y_mul_invY, one_pow, mul_one]

open Algebra.TensorProduct in
theorem productMap_BA_surjective :
    Function.Surjective (productMap (BtoAyₐ k) (IsScalarTower.toAlgHom k (A k) (Ay k))) := by
  intro z
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (yA k) z
  refine ⟨(wB k ^ n) ⊗ₜ a, ?_⟩
  have hw : BtoAyₐ k (wB k) = invY k := by
    change BtoAy k (wB k) = _; rw [BtoAy, liftB_w]
  rw [productMap_apply_tmul, map_pow, hw, IsScalarTower.coe_toAlgHom', ← h, mul_comm,
    mul_assoc, ← mul_pow, y_mul_invY, one_pow, mul_one]

open Algebra.TensorProduct in
theorem productMap_id_surjective (R : Type u) [CommRing R] [Algebra k R] :
    Function.Surjective (productMap (AlgHom.id k R) (AlgHom.id k R)) :=
  fun z => ⟨z ⊗ₜ 1, by simp⟩

theorem isPullback_id_of_mono {R : Type u} [CommRing R] [Algebra k R] {X : Scheme.{u}}
    (u : Spec (.of R) ⟶ X) [Mono u] :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.id k R).toRingHom))
      (Spec.map (CommRingCat.ofHom (AlgHom.id k R).toRingHom)) u u := by
  have h : Spec.map (CommRingCat.ofHom (AlgHom.id k R).toRingHom) = 𝟙 _ := by
    rw [← Spec.map_id]; rfl
  rw [h]
  exact IsKernelPair.id_of_mono u

/-- **Step (3).** `E ⟶ Spec k` is separated. -/
instance toSpec_isSeparated : IsSeparated (toSpec k) := by
  constructor
  let 𝒰 := (glueData k).openCover
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 (toSpec k) (toSpec k))]
  rintro ⟨a, b⟩
  change IsClosedImmersion (pullback.snd (pullback.diagonal (toSpec k))
    (pullback.map (𝒰.f a ≫ toSpec k) (𝒰.f b ≫ toSpec k) (toSpec k) (toSpec k) (𝒰.f a) (𝒰.f b)
      (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  have : pullback.snd (pullback.diagonal (toSpec k))
      (pullback.map (𝒰.f a ≫ toSpec k) (𝒰.f b ≫ toSpec k) (toSpec k) (toSpec k) (𝒰.f a) (𝒰.f b)
        (𝟙 _) (Category.comp_id _) (Category.comp_id _)) =
      (pullbackDiagonalMapIdIso (𝒰.f a) (𝒰.f b) (toSpec k)).hom ≫
        pullback.map (𝒰.f a) (𝒰.f b) (𝒰.f a ≫ toSpec k) (𝒰.f b ≫ toSpec k) (𝟙 _) (𝟙 _)
          (toSpec k) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [this, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  rcases a with ⟨_ | _⟩ <;> rcases b with ⟨_ | _⟩
  · exact isClosedImmersion_pullback_map_of_affine (toSpec k) (ιA k) (ιA k) (ιA_toSpec k)
      (ιA_toSpec k) (AlgHom.id k _) (AlgHom.id k _) (isPullback_id_of_mono k _)
      (productMap_id_surjective k _)
  · exact isClosedImmersion_pullback_map_of_affine (toSpec k) (ιA k) (ιB k) (ιA_toSpec k)
      (ιB_toSpec k) (IsScalarTower.toAlgHom k (A k) (Ay k)) (BtoAyₐ k) (isPullback_charts k)
      (productMap_AB_surjective k)
  · exact isClosedImmersion_pullback_map_of_affine (toSpec k) (ιB k) (ιA k) (ιB_toSpec k)
      (ιA_toSpec k) (BtoAyₐ k) (IsScalarTower.toAlgHom k (A k) (Ay k))
      (isPullback_charts k).flip (productMap_BA_surjective k)
  · exact isClosedImmersion_pullback_map_of_affine (toSpec k) (ιB k) (ιB k) (ιB_toSpec k)
      (ιB_toSpec k) (AlgHom.id k _) (AlgHom.id k _) (isPullback_id_of_mono k _)
      (productMap_id_surjective k _)

end Separated

#print axioms isPullback_charts
#print axioms toSpec_locallyOfFiniteType
#print axioms toSpec_quasiCompact
#print axioms isIntegral
#print axioms toSpec_isSeparated

end Pcf.Examples.PaperP.MonodromyLossCurve
