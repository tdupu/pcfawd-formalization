/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSmoothRestriction
public import Pcf.PaperCharZero.SupportingTower
public import Pcf.Bounding.GlobalNormalizationIteration
public import Pcf.Bounding.SmoothRegularLocal
public import Pcf.Bounding.NormalSchemePCFComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Geometric branch assertions for the smooth-restriction example

Uses actual affine schemes, their canonical normalizations and the manuscript's
normalized branch support. The ambient residue-field fiber is explicitly
isomorphic to `κ(p)[T]/(T²-x̄)`, so its nonreduced fibers and unique branch
divisor are calculated directly. The parabola is a smooth integral divisor;
the normalized restriction has empty branch support, while its intersection
with the ambient normalized branch support is the origin. An explicit rank-two
basis and coincident first-order defining ideals supply the freeness and
tangency assertions. No branch or PCF assertion is an input.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperSmoothBranch

open CategoryTheory AlgebraicGeometry Polynomial
open scoped TensorProduct
open CharZeroPaperSmoothRestriction Pcf.PaperCharZero

universe u
variable (K : Type u) [Field K]

attribute [local instance] ambient_finite ambient_surjective

instance lineRing_isDomain : IsDomain (LineRing K) :=
  (lineEquiv K).toRingEquiv.isDomain_iff.mpr inferInstance

instance parabolaRing_isDomain : IsDomain (ParabolaRing K) :=
  (parabolaEquiv K).toRingEquiv.isDomain_iff.mpr inferInstance

instance line_isIntegral : IsIntegral (line K) := inferInstance
instance parabola_isIntegral : IsIntegral (parabola K) := inferInstance

/-- An isomorphism induces an isomorphism on the actual canonical normalizations. -/
theorem normalizationMorphism_isIso_of_isIso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsIso f] : IsIso (schemeGlobalNormalizationMorphism f) := by
  refine ⟨⟨schemeGlobalNormalizationMorphism (inv f), ?_, ?_⟩⟩
  · simp only [schemeGlobalNormalizationMorphism_comp_morphism, IsIso.hom_inv_id,
      schemeGlobalNormalizationMorphism_id]
  · simp only [schemeGlobalNormalizationMorphism_comp_morphism, IsIso.inv_hom_id,
      schemeGlobalNormalizationMorphism_id]

/-- An isomorphism has reduced actual fibers at all scheme points. -/
theorem iso_fiber_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (y : Y) :
    IsReduced (f.fiber y) := by
  let : IsIso (f.fiberToSpecResidueField y) :=
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).isIso_snd_of_isIso
  exact isReduced_of_isOpenImmersion (f.fiberToSpecResidueField y)

/-- This is the project's actual codimension-one reduced-fiber branch definition. -/
theorem iso_reducedFiberBranch_empty {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    schemeReducedFiberBranch f = ∅ := by
  ext E
  simp only [schemeReducedFiberBranch, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact iso_fiber_isReduced f E.1

/-- Source-shaped normalized branch support vanishes for an actual isomorphism. -/
theorem iso_normalizedMorphismBranchSupport_empty
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsIso f] : normalizedMorphismBranchSupport f = ∅ := by
  let : IsIso (schemeGlobalNormalizationMorphism f) := normalizationMorphism_isIso_of_isIso f
  simp [normalizedMorphismBranchSupport, iso_reducedFiberBranch_empty, divisorSupport]

/-- The actual normalized restriction in `ex:smooth-restriction` is an isomorphism. -/
theorem normalized_restriction_isIso :
    IsIso (schemeGlobalNormalizationMorphism (restrictionMap K)) :=
  normalizationMorphism_isIso_of_isIso _

/-- The manuscript's normalized branch support of the actual parabola restriction is empty. -/
theorem normalized_restriction_branch_empty :
    normalizedMorphismBranchSupport (restrictionMap K) = ∅ :=
  iso_normalizedMorphismBranchSupport_empty _

/-- The structural morphism from the plane to its coefficient field. -/
def planeStructure : plane K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (PlaneRing K)))

/-- The structural morphism from the actual parabola quotient. -/
def parabolaStructure : parabola K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ParabolaRing K)))

instance planeStructure_smooth : Smooth (planeStructure K) := by
  let : Algebra.Smooth K (Polynomial K) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth (Polynomial K) (PlaneRing K) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth K (PlaneRing K) := Algebra.Smooth.comp K (Polynomial K) _
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

instance parabolaStructure_smooth : Smooth (parabolaStructure K) := by
  let : Algebra.Smooth K (Polynomial K) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth K (ParabolaRing K) :=
    Algebra.Smooth.of_equiv ((parabolaEquiv K).restrictScalars K).symm
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The quotient curve sits over the same coefficient field as the plane. -/
theorem parabolaStructure_commutes :
    parabolaImmersion K ≫ planeStructure K = parabolaStructure K := by
  simp only [parabolaImmersion, planeStructure, parabolaStructure, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

instance parabolaIdeal_isPrime : (parabolaIdeal K).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- The actual defining ideal of the parabola is a height-one prime ideal. -/
theorem parabolaIdeal_height : (parabolaIdeal K).height = 1 := by
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (X_sub_C_ne_zero _)) (not_isUnit_X_sub_C _)

/-- The parabola gives a genuine codimension-one point of the ambient scheme. -/
def parabolaDivisorPoint : SchemeDivisorPoint (plane K) :=
  ⟨⟨parabolaIdeal K, inferInstance⟩,
    (idealHeight_eq_coheight (.of (PlaneRing K)) ⟨parabolaIdeal K, inferInstance⟩).symm.trans
      (parabolaIdeal_height K)⟩

/-- Its closed support is the image of the actual closed immersion. -/
theorem parabola_range_eq_divisorClosure :
    Set.range (parabolaImmersion K) =
      closure ({(parabolaDivisorPoint K).1} : Set (plane K)) := by
  change Set.range (PrimeSpectrum.comap (R := PlaneRing K) (S := ParabolaRing K)
    (Ideal.Quotient.mk (parabolaIdeal K))) =
      closure ({⟨parabolaIdeal K, inferInstance⟩} : Set (PrimeSpectrum (PlaneRing K)))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    PrimeSpectrum.closure_singleton, Ideal.mk_ker]

/-- A monic presentation of the ambient degree-two algebra. -/
def ambientRelation : Polynomial (PlaneRing K) := X ^ 2 - C X

def presentationToSource : AdjoinRoot (ambientRelation K) →+* PlaneRing K :=
  AdjoinRoot.lift (ambientPullback K) X (by simp [ambientRelation])

def sourceToPresentation : PlaneRing K →+* AdjoinRoot (ambientRelation K) :=
  Polynomial.eval₂RingHom ((AdjoinRoot.of (ambientRelation K)).comp C)
    (AdjoinRoot.root (ambientRelation K))

@[simp] theorem sourceToPresentation_C (p : Polynomial K) :
    sourceToPresentation K (C p) = AdjoinRoot.of (ambientRelation K) (C p) := by
  simp [sourceToPresentation]

@[simp] theorem sourceToPresentation_X :
    sourceToPresentation K X = AdjoinRoot.root (ambientRelation K) := by
  simp [sourceToPresentation]

theorem presentation_root_sq :
    AdjoinRoot.root (ambientRelation K) ^ 2 = AdjoinRoot.of (ambientRelation K) X := by
  have h : eval₂ (AdjoinRoot.of (ambientRelation K)) (AdjoinRoot.root (ambientRelation K))
      (X ^ 2 - C (X : PlaneRing K)) = 0 := AdjoinRoot.eval₂_root (ambientRelation K)
  simpa only [ eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h

theorem presentationToSource_comp_source :
    (presentationToSource K).comp (sourceToPresentation K) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro p; simp [RingHom.comp_apply, presentationToSource]
  · simp [RingHom.comp_apply, presentationToSource]

theorem sourceToPresentation_comp_ambient :
    (sourceToPresentation K).comp (ambientPullback K) = AdjoinRoot.of (ambientRelation K) := by
  apply Polynomial.ringHom_ext
  · intro p; simp [RingHom.comp_apply]
  · simp [RingHom.comp_apply, presentation_root_sq]

theorem source_comp_presentationToSource :
    (sourceToPresentation K).comp (presentationToSource K) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · simp only [RingHom.comp_assoc, presentationToSource, AdjoinRoot.lift_comp_of,
      RingHom.id_comp]
    exact sourceToPresentation_comp_ambient K
  · simp [RingHom.comp_apply, presentationToSource]

def ambientPresentationEquiv : AdjoinRoot (ambientRelation K) ≃+* PlaneRing K :=
  RingEquiv.ofRingHom (presentationToSource K) (sourceToPresentation K)
    (presentationToSource_comp_source K) (source_comp_presentationToSource K)

/-- A separate type for the source ring prevents the nonidentity target action
from being confused with the ring's usual self-action. -/
def AmbientSourceRing := PlaneRing K
instance ambientSourceCommRing : CommRing (AmbientSourceRing K) :=
  inferInstanceAs (CommRing (PlaneRing K))
instance ambientSourceAlgebra : Algebra (PlaneRing K) (AmbientSourceRing K) :=
  (show PlaneRing K →+* AmbientSourceRing K from ambientPullback K).toAlgebra

/-- The presentation respects the actual ambient pullback algebra. -/
def ambientPresentationAlgEquiv :
    AdjoinRoot (ambientRelation K) ≃ₐ[PlaneRing K] AmbientSourceRing K :=
  { ambientPresentationEquiv K with commutes' := fun _ => AdjoinRoot.lift_of _ }

/-- The actual residue-field tensor product has the expected quadratic presentation. -/
def ambientFiberEquiv (p : PrimeSpectrum (PlaneRing K)) :
    p.asIdeal.Fiber (AmbientSourceRing K) ≃+*
      AdjoinRoot (X ^ 2 - C (algebraMap (PlaneRing K) p.asIdeal.ResidueField X)) := by
  let e₁ := Algebra.TensorProduct.congr
    (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
    (ambientPresentationAlgEquiv K).symm
  let q := (ambientRelation K).map
    (Algebra.TensorProduct.includeRight : PlaneRing K →ₐ[PlaneRing K]
      p.asIdeal.ResidueField ⊗[PlaneRing K] PlaneRing K).toRingHom
  let e₂ := AdjoinRoot.tensorAlgEquiv (R := PlaneRing K) (T := p.asIdeal.ResidueField)
    (ambientRelation K) q rfl
  let e₃ := AdjoinRoot.mapAlgEquiv
    (Algebra.TensorProduct.rid (PlaneRing K) p.asIdeal.ResidueField p.asIdeal.ResidueField)
    q (X ^ 2 - C (algebraMap (PlaneRing K) p.asIdeal.ResidueField X))
    (Associated.of_eq (by simp [q, ambientRelation, Algebra.smul_def]))
  exact e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv)

/-- Over a characteristic-zero field, the quadratic fiber algebra is reduced
exactly when its constant parameter is nonzero. -/
theorem quadratic_isReduced_iff {F : Type u} [Field F] [CharZero F] (a : F) :
    _root_.IsReduced (AdjoinRoot (X ^ 2 - C a)) ↔ a ≠ 0 := by
  constructor
  · intro hred ha
    let : _root_.IsReduced (AdjoinRoot (X ^ 2 - C a)) := hred
    have hroot : AdjoinRoot.root (X ^ 2 - C a) ≠ 0 :=
      AdjoinRoot.mk_ne_zero_of_degree_lt (monic_X_pow_sub_C a (by decide)) X_ne_zero
        (by rw [degree_X, degree_X_pow_sub_C (by decide)]; norm_num)
    apply hroot
    apply IsNilpotent.eq_zero
    refine ⟨2, ?_⟩
    have h := AdjoinRoot.eval₂_root (X ^ 2 - C a)
    simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ha, map_zero, sub_zero] using h
  · intro ha
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    apply isRadical_iff_span_singleton.mp
    exact (separable_X_pow_sub_C a (by norm_num : (2 : F) ≠ 0) ha).squarefree.isRadical

set_option backward.isDefEq.respectTransparency false in
/-- Reducedness comparison for the actual affine-scheme fiber. -/
theorem ambient_fiber_isReduced_iff_ring (p : PrimeSpectrum (PlaneRing K)) :
    IsReduced ((ambientMap K).fiber p) ↔
      _root_.IsReduced (p.asIdeal.Fiber (AmbientSourceRing K)) := by
  let e := Spec.fiberToSpecResidueFieldIso (PlaneRing K) (AmbientSourceRing K) p
  constructor
  · intro h
    exact (affine_isReduced_iff _).mp
      (@isReduced_of_isOpenImmersion _ _ e.inv.left inferInstance h)
  · intro h
    let : IsIso e.hom.left := (Arrow.leftFunc.mapIso e).isIso_hom
    have hspec := (affine_isReduced_iff (.of (p.asIdeal.Fiber (AmbientSourceRing K)))).mpr h
    exact @isReduced_of_isOpenImmersion _ _ e.hom.left (IsOpenImmersion.of_isIso _) hspec

/-- The actual squaring map has a nonreduced fiber precisely over `x=0`. -/
theorem ambient_fiber_isReduced_iff [CharZero K] (p : PrimeSpectrum (PlaneRing K)) :
    IsReduced ((ambientMap K).fiber p) ↔ (X : PlaneRing K) ∉ p.asIdeal := by
  rw [ambient_fiber_isReduced_iff_ring]
  let : Algebra K p.asIdeal.ResidueField :=
    ((algebraMap (PlaneRing K) p.asIdeal.ResidueField).comp
      (algebraMap K (PlaneRing K))).toAlgebra
  let : CharZero p.asIdeal.ResidueField := Algebra.charZero_of_charZero K _
  have he : _root_.IsReduced (p.asIdeal.Fiber (AmbientSourceRing K)) ↔
      _root_.IsReduced (AdjoinRoot
        (X ^ 2 - C (algebraMap (PlaneRing K) p.asIdeal.ResidueField X))) := by
    constructor
    · intro h
      let : _root_.IsReduced (p.asIdeal.Fiber (AmbientSourceRing K)) := h
      exact isReduced_of_injective (ambientFiberEquiv K p).symm
        (ambientFiberEquiv K p).symm.injective
    · intro h
      let : _root_.IsReduced
          (AdjoinRoot (X ^ 2 - C (algebraMap (PlaneRing K) p.asIdeal.ResidueField X))) := h
      exact isReduced_of_injective (ambientFiberEquiv K p) (ambientFiberEquiv K p).injective
  rw [he, quadratic_isReduced_iff, ne_eq, Ideal.algebraMap_residueField_eq_zero]

def axisIdeal : Ideal (PlaneRing K) := Ideal.span {X}

instance axisIdeal_isPrime : (axisIdeal K).IsPrime :=
  (Ideal.span_singleton_prime X_ne_zero).mpr prime_X

theorem axisIdeal_height : (axisIdeal K).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr X_ne_zero) (not_isUnit_X : ¬ IsUnit (X : PlaneRing K))

def axisDivisorPoint : SchemeDivisorPoint (plane K) :=
  ⟨⟨axisIdeal K, inferInstance⟩,
    (idealHeight_eq_coheight (.of (PlaneRing K)) ⟨axisIdeal K, inferInstance⟩).symm.trans
      (axisIdeal_height K)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sole actual codimension-one nonreduced-fiber divisor is `x=0`. -/
theorem ambient_reducedFiberBranch [CharZero K] :
    schemeReducedFiberBranch (ambientMap K) = {axisDivisorPoint K} := by
  ext Q
  change (¬ IsReduced ((ambientMap K).fiber Q.1)) ↔ Q = axisDivisorPoint K
  rw [ambient_fiber_isReduced_iff, not_not]
  constructor
  · intro hx
    have hheight : Q.1.asIdeal.height = 1 :=
      (idealHeight_eq_coheight (.of (PlaneRing K)) Q.1).trans Q.2
    let : (axisIdeal K).FiniteHeight := by
      simp [Ideal.finiteHeight_iff, axisIdeal_height]
    have he : axisIdeal K = Q.1.asIdeal := Ideal.eq_of_le_of_height_le (axisIdeal K)
      (Ideal.span_le.mpr (by simpa using hx)) (by rw [hheight, axisIdeal_height])
    apply Subtype.ext
    exact PrimeSpectrum.ext he.symm
  · rintro rfl
    exact Ideal.subset_span (Set.mem_singleton _)

set_option backward.isDefEq.respectTransparency false in
/-- Actual codimension-one branch support is exactly the coordinate axis. -/
theorem ambient_reducedFiberBranch_support [CharZero K] :
    divisorSupport (schemeReducedFiberBranch (ambientMap K)) =
      {p : plane K | (X : PlaneRing K) ∈ p.asIdeal} := by
  rw [ambient_reducedFiberBranch]
  simp only [divisorSupport, Set.biUnion_singleton]
  change closure ({⟨axisIdeal K, inferInstance⟩} : Set (PrimeSpectrum (PlaneRing K))) = _
  rw [PrimeSpectrum.closure_singleton]
  ext p
  change axisIdeal K ≤ p.asIdeal ↔ (X : PlaneRing K) ∈ p.asIdeal
  simp [axisIdeal, Ideal.span_le]

/-- A spectrum of an integrally closed domain is normal in the project's
all-affine-open sense; the proof passes through the actual local rings. -/
theorem normal_spec (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalScheme (Spec (.of R)) := by
  apply isNormalScheme_of_stalk_integrallyClosed
  intro p
  let p' : PrimeSpectrum R := p
  let : p'.asIdeal.IsPrime := p'.isPrime
  let : IsIntegrallyClosed (Localization.AtPrime p'.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p'.asIdeal)
      p'.asIdeal.primeCompl p'.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (R := Localization.AtPrime p'.asIdeal)
    (Spec.stalkIso (.of R) p').symm.commRingCatIsoToRingEquiv

instance plane_isNormal : IsNormalScheme (plane K) := normal_spec (PlaneRing K)

instance line_isNormal : IsNormalScheme (line K) := by
  let : IsIntegrallyClosed (LineRing K) :=
    IsIntegrallyClosed.of_equiv (lineEquiv K).symm.toRingEquiv
  exact normal_spec _

instance parabola_isNormal : IsNormalScheme (parabola K) := by
  let : IsIntegrallyClosed (ParabolaRing K) :=
    IsIntegrallyClosed.of_equiv (parabolaEquiv K).symm.toRingEquiv
  exact normal_spec _

theorem line_normalization_isIso : IsIso (Palomar.normalizationMap (line K)) :=
  normalScheme_normalizationMap_isIso _

theorem parabola_normalization_isIso : IsIso (Palomar.normalizationMap (parabola K)) :=
  normalScheme_normalizationMap_isIso _

/-- For normal Noetherian schemes, canonical normalized branch support agrees
with actual codimension-one nonreduced-fiber support. -/
theorem normalized_support_eq_reduced_support
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    normalizedMorphismBranchSupport f = divisorSupport (schemeReducedFiberBranch f) := by
  let : IsIso (Palomar.normalizationMap X) := normalScheme_normalizationMap_isIso X
  let : IsIso (Palomar.normalizationMap Y) := normalScheme_normalizationMap_isIso Y
  let : IsLocallyNoetherian (Palomar.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap X)
  let : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Y)
  have h₁ := reducedFiberBranch_support_tower
    (schemeGlobalNormalizationMorphism f) (Palomar.normalizationMap Y)
  have h₂ := reducedFiberBranch_support_tower (Palomar.normalizationMap X) f
  rw [schemeGlobalNormalizationMorphism_comp] at h₁
  rw [h₂] at h₁
  simpa only [normalizedMorphismBranchSupport, iso_reducedFiberBranch_empty,
    divisorSupport, Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty,
    Set.image_empty, Set.union_empty, Set.empty_union] using h₁.symm

/-- The actual normalized ambient branch support is the axis `x=0`. -/
theorem normalized_ambient_branch [CharZero K] :
    normalizedMorphismBranchSupport (ambientMap K) =
      {p : plane K | (X : PlaneRing K) ∈ p.asIdeal} := by
  let : IsFinite (ambientMap K) := ambient_finite K
  let : Surjective (ambientMap K) := ambient_surjective K
  rw [normalized_support_eq_reduced_support, ambient_reducedFiberBranch_support]

def originIdeal : Ideal (PlaneRing K) := Ideal.span {C X, X}

set_option backward.isDefEq.respectTransparency false in
def originQuotientEquiv : (PlaneRing K ⧸ originIdeal K) ≃ₐ[K] K := by
  let I : Ideal (PlaneRing K) := Ideal.span {C (X - C (0 : K)), X - C (0 : Polynomial K)}
  have hI : originIdeal K = I := by
    dsimp [originIdeal, I]
    rw [show C (0 : K) = 0 from map_zero C,
      show C (0 : Polynomial K) = 0 from map_zero C, sub_zero, sub_zero]
  exact (Ideal.quotientEquivAlgOfEq K hI).trans
    (Polynomial.quotientSpanCXSubCXSubCAlgEquiv (x := (0 : K)) (y := (0 : Polynomial K)))

instance originIdeal_isMaximal : (originIdeal K).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((originQuotientEquiv K).toMulEquiv.isField (Field.toIsField K))

def origin : plane K := ⟨originIdeal K, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the support of the actual parabola immersion. -/
theorem mem_parabola_range_iff (p : plane K) :
    p ∈ Set.range (parabolaImmersion K) ↔ (X - C (X ^ 2) : PlaneRing K) ∈ p.asIdeal := by
  rw [parabola_range_eq_divisorClosure]
  change p ∈ closure ({⟨parabolaIdeal K, inferInstance⟩} : Set (PrimeSpectrum (PlaneRing K))) ↔ _
  rw [PrimeSpectrum.closure_singleton]
  change parabolaIdeal K ≤ p.asIdeal ↔ _
  simp [parabolaIdeal, Ideal.span_le]

set_option backward.isDefEq.respectTransparency false in
/-- The actual parabola and normalized ambient branch support meet only at the origin. -/
theorem parabola_inter_normalized_ambient_branch [CharZero K] :
    Set.range (parabolaImmersion K) ∩ normalizedMorphismBranchSupport (ambientMap K) =
      {origin K} := by
  rw [normalized_ambient_branch]
  ext p
  simp only [Set.mem_inter_iff, mem_parabola_range_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hx⟩
    have hcy2 : C (X ^ 2 : Polynomial K) ∈ p.asIdeal := by
      convert p.asIdeal.sub_mem hx hp using 1; ring
    have hcy : C (X : Polynomial K) ∈ p.asIdeal :=
      p.isPrime.mem_of_pow_mem 2 (by simpa only [map_pow] using hcy2)
    have hle : originIdeal K ≤ p.asIdeal := Ideal.span_le.mpr (by
      intro t ht
      rcases ht with rfl | ht
      · exact hcy
      · simpa only [Set.mem_singleton_iff] using ht ▸ hx)
    exact PrimeSpectrum.ext ((originIdeal_isMaximal K).eq_of_le p.isPrime.ne_top hle).symm
  · rintro rfl
    have hx : (X : PlaneRing K) ∈ originIdeal K := Ideal.subset_span (by simp)
    have hy : C (X : Polynomial K) ∈ originIdeal K := Ideal.subset_span (by simp)
    refine ⟨?_, hx⟩
    apply (originIdeal K).sub_mem hx
    have he : (C (X ^ 2 : Polynomial K) : PlaneRing K) = C X * C X := by
      rw [Polynomial.C_pow, pow_two]
    rw [he]
    exact (originIdeal K).mul_mem_left (C (X : Polynomial K)) hy

/-- `ex:smooth-restriction`: strict inclusion for actual normalized branch
supports, with both sides regarded as subsets of the ambient target scheme. -/
theorem normalized_branch_strict_inclusion [CharZero K] :
    (parabolaImmersion K) '' normalizedMorphismBranchSupport (restrictionMap K) ⊂
      Set.range (parabolaImmersion K) ∩ normalizedMorphismBranchSupport (ambientMap K) := by
  rw [normalized_restriction_branch_empty, Set.image_empty,
    parabola_inter_normalized_ambient_branch]
  exact Set.empty_ssubset.mpr ⟨origin K, rfl⟩

/-- An explicit basis with two elements for the ambient coordinate-ring extension. -/
def ambientBasis : Module.Basis (Fin 2) (PlaneRing K) (AmbientSourceRing K) := by
  have hm : (ambientRelation K).Monic := monic_X_pow_sub_C _ (by decide)
  have hd : (ambientRelation K).natDegree = 2 := natDegree_X_pow_sub_C
  exact ((AdjoinRoot.powerBasis' hm).basis.reindex (finCongr hd)).map
    (ambientPresentationAlgEquiv K).toLinearEquiv

/-- Every local ring of the ambient plane is regular. -/
theorem plane_stalk_regular (p : plane K) : IsRegularLocalRing ((plane K).presheaf.stalk p) := by
  exact isRegularLocalRing_stalk_of_mem_smoothLocus (.of K) (planeStructure K) p
    (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)

/-- Every local ring of the actual parabola is regular. -/
theorem parabola_stalk_regular (p : parabola K) :
    IsRegularLocalRing ((parabola K).presheaf.stalk p) := by
  exact isRegularLocalRing_stalk_of_mem_smoothLocus (.of K) (parabolaStructure K) p
    (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)

/-- The parabola and coordinate axis have identical first-order defining ideals
at the origin. This is the explicit tangent-equation certificate. -/
theorem tangent_ideals_equal :
    parabolaIdeal K ⊔ originIdeal K ^ 2 = axisIdeal K ⊔ originIdeal K ^ 2 := by
  have hy : C (X : Polynomial K) ∈ originIdeal K := Ideal.subset_span (by simp)
  have hy2 : C (X ^ 2 : Polynomial K) ∈ originIdeal K ^ 2 := by
    simpa only [Polynomial.C_pow] using Ideal.pow_mem_pow hy 2
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact (axisIdeal K ⊔ originIdeal K ^ 2).sub_mem
      (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))) (Ideal.mem_sup_right hy2)
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ rfl
    have h := (parabolaIdeal K ⊔ originIdeal K ^ 2).add_mem
      (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton (X - C (X ^ 2) : PlaneRing K))))
      (Ideal.mem_sup_right hy2)
    change (X : PlaneRing K) ∈ parabolaIdeal K ⊔ originIdeal K ^ 2
    simpa only [sub_add_cancel] using h

/-- Formal partial differentiation in the coefficient variable `y` of `K[y][x]`. -/
def coefficientPartial (p : PlaneRing K) : PlaneRing K :=
  p.sum fun n a => C (Polynomial.derivative a) * X ^ n

@[simp] theorem coefficientPartial_X_sq : coefficientPartial K (X ^ 2) = 0 := by
  simp [coefficientPartial, ← Polynomial.monomial_one_right_eq_X_pow]

@[simp] theorem coefficientPartial_C_X : coefficientPartial K (C X) = 1 := by
  simp [coefficientPartial]

/-- The actual formal Jacobian determinant of `(u²,v)` is `2u`. -/
theorem ambient_jacobian :
    Matrix.det !![Polynomial.derivative (ambientPullback K X),
        coefficientPartial K (ambientPullback K X);
      Polynomial.derivative (ambientPullback K (C X)),
        coefficientPartial K (ambientPullback K (C X))] = 2 * (X : PlaneRing K) := by
  norm_num [Matrix.det_fin_two]
  exact map_ofNat C 2

#print axioms coefficientPartial
#check @coefficientPartial
#print axioms coefficientPartial_X_sq
#check @coefficientPartial_X_sq
#print axioms coefficientPartial_C_X
#check @coefficientPartial_C_X
#print axioms ambient_jacobian
#check @ambient_jacobian

#print axioms lineRing_isDomain
#check @lineRing_isDomain
#print axioms parabolaRing_isDomain
#check @parabolaRing_isDomain
#print axioms line_isIntegral
#check @line_isIntegral
#print axioms parabola_isIntegral
#check @parabola_isIntegral
#print axioms normalizationMorphism_isIso_of_isIso
#check @normalizationMorphism_isIso_of_isIso
#print axioms iso_fiber_isReduced
#check @iso_fiber_isReduced
#print axioms iso_reducedFiberBranch_empty
#check @iso_reducedFiberBranch_empty
#print axioms iso_normalizedMorphismBranchSupport_empty
#check @iso_normalizedMorphismBranchSupport_empty
#print axioms normalized_restriction_isIso
#check @normalized_restriction_isIso
#print axioms normalized_restriction_branch_empty
#check @normalized_restriction_branch_empty
#print axioms planeStructure
#check @planeStructure
#print axioms parabolaStructure
#check @parabolaStructure
#print axioms planeStructure_smooth
#check @planeStructure_smooth
#print axioms parabolaStructure_smooth
#check @parabolaStructure_smooth
#print axioms parabolaStructure_commutes
#check @parabolaStructure_commutes
#print axioms parabolaIdeal_isPrime
#check @parabolaIdeal_isPrime
#print axioms parabolaIdeal_height
#check @parabolaIdeal_height
#print axioms parabolaDivisorPoint
#check @parabolaDivisorPoint
#print axioms parabola_range_eq_divisorClosure
#check @parabola_range_eq_divisorClosure
#print axioms ambientRelation
#check @ambientRelation
#print axioms presentationToSource
#check @presentationToSource
#print axioms sourceToPresentation
#check @sourceToPresentation
#print axioms sourceToPresentation_C
#check @sourceToPresentation_C
#print axioms sourceToPresentation_X
#check @sourceToPresentation_X
#print axioms presentation_root_sq
#check @presentation_root_sq
#print axioms presentationToSource_comp_source
#check @presentationToSource_comp_source
#print axioms sourceToPresentation_comp_ambient
#check @sourceToPresentation_comp_ambient
#print axioms source_comp_presentationToSource
#check @source_comp_presentationToSource
#print axioms ambientPresentationEquiv
#check @ambientPresentationEquiv
#print axioms AmbientSourceRing
#check @AmbientSourceRing
#print axioms ambientSourceCommRing
#check @ambientSourceCommRing
#print axioms ambientSourceAlgebra
#check @ambientSourceAlgebra
#print axioms ambientPresentationAlgEquiv
#check @ambientPresentationAlgEquiv
#print axioms ambientFiberEquiv
#check @ambientFiberEquiv
#print axioms quadratic_isReduced_iff
#check @quadratic_isReduced_iff
#print axioms ambient_fiber_isReduced_iff_ring
#check @ambient_fiber_isReduced_iff_ring
#print axioms ambient_fiber_isReduced_iff
#check @ambient_fiber_isReduced_iff
#print axioms axisIdeal
#check @axisIdeal
#print axioms axisIdeal_isPrime
#check @axisIdeal_isPrime
#print axioms axisIdeal_height
#check @axisIdeal_height
#print axioms axisDivisorPoint
#check @axisDivisorPoint
#print axioms ambient_reducedFiberBranch
#check @ambient_reducedFiberBranch
#print axioms ambient_reducedFiberBranch_support
#check @ambient_reducedFiberBranch_support
#print axioms normal_spec
#check @normal_spec
#print axioms plane_isNormal
#check @plane_isNormal
#print axioms line_isNormal
#check @line_isNormal
#print axioms parabola_isNormal
#check @parabola_isNormal
#print axioms line_normalization_isIso
#check @line_normalization_isIso
#print axioms parabola_normalization_isIso
#check @parabola_normalization_isIso
#print axioms normalized_support_eq_reduced_support
#check @normalized_support_eq_reduced_support
#print axioms normalized_ambient_branch
#check @normalized_ambient_branch
#print axioms originIdeal
#check @originIdeal
#print axioms originQuotientEquiv
#check @originQuotientEquiv
#print axioms originIdeal_isMaximal
#check @originIdeal_isMaximal
#print axioms origin
#check @origin
#print axioms mem_parabola_range_iff
#check @mem_parabola_range_iff
#print axioms parabola_inter_normalized_ambient_branch
#check @parabola_inter_normalized_ambient_branch
#print axioms normalized_branch_strict_inclusion
#check @normalized_branch_strict_inclusion
#print axioms ambientBasis
#check @ambientBasis
#print axioms plane_stalk_regular
#check @plane_stalk_regular
#print axioms parabola_stalk_regular
#check @parabola_stalk_regular
#print axioms tangent_ideals_equal
#check @tangent_ideals_equal

end Pcf.Examples.CharZeroPaperSmoothBranch
