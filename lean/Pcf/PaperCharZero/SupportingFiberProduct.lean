/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingTower
public import Pcf.PaperCharZero.SupportingNormalizationLift
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generic divisor fibers

The product presentation and reducedness criterion in `paper.tex`, `u:fibre-product`.
The ring presentation uses the spectrum of the actual fiber as its index type;
its points correspond to the integral effective divisors over the target divisor.
-/

@[expose] public section

universe u
open AlgebraicGeometry CategoryTheory

namespace Pcf.PaperCharZero

noncomputable section

/-- The product of the source local DVR quotients indexed by the actual fiber. -/
abbrev divisorFiberProductRing {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : HeightOnePrime R) :=
  ∀ q : PrimeSpectrum (p.1.asIdeal.Fiber S),
    Localization.AtPrime (q.asIdeal.comap Algebra.TensorProduct.includeRight) ⧸
      IsLocalRing.maximalIdeal
        (Localization.AtPrime (q.asIdeal.comap Algebra.TensorProduct.includeRight)) ^
          (q.asIdeal.comap Algebra.TensorProduct.includeRight).ramificationIdx R

section Rings

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S]
  [Module.Finite R S] [FaithfulSMul R S]

omit [IsDomain R] in
/-- The pullback of the target divisor ideal to the source DVR is exactly
its maximal ideal to the ramification-index power. -/
theorem divisorFiber_local_ideal_eq_power (p : HeightOnePrime R)
    (Q : HeightOnePrime S) [Q.1.asIdeal.LiesOver p.1.asIdeal] :
    p.1.asIdeal.map (algebraMap R (Localization.AtPrime Q.1.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q.1.asIdeal) ^
        heightOneRamificationIdx (R := R) Q := by
  rw [heightOneRamificationIdx_eq_dvrExponent (R := R) Q]
  simpa only [show Q.1.asIdeal.under R = p.1.asIdeal from
    (Ideal.LiesOver.over (p := p.1.asIdeal) (P := Q.1.asIdeal)).symm] using
    heightOneDvrExponent_spec (R := R) Q

/-- The actual finite fiber algebra is the product of the local Artinian
quotients `S_q / m_q^e`. No reducedness or decomposition premise is assumed. -/
def divisorFiber_product_equiv (p : HeightOnePrime R) :
    p.1.asIdeal.Fiber S ≃+*
      ∀ q : PrimeSpectrum (p.1.asIdeal.Fiber S),
        Localization.AtPrime (q.asIdeal.comap Algebra.TensorProduct.includeRight) ⧸
          IsLocalRing.maximalIdeal
            (Localization.AtPrime (q.asIdeal.comap Algebra.TensorProduct.includeRight)) ^
              (q.asIdeal.comap Algebra.TensorProduct.includeRight).ramificationIdx R := by
  let e := (PrimeSpectrum.toPiLocalizationEquiv (p.1.asIdeal.Fiber S)).toRingEquiv
  refine e.trans (RingEquiv.piCongrRight fun q ↦ ?_)
  let r : Ideal S := q.asIdeal.comap Algebra.TensorProduct.includeRight
  let Q : HeightOnePrime S :=
    ⟨⟨r, inferInstance⟩,
      height_eq_one_of_liesOver_heightOne r p.1.asIdeal inferInstance p.2⟩
  let : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p.1.asIdeal r
  exact (Ideal.Fiber.localizationAlgEquivQuotient p.1.asIdeal q.asIdeal).toRingEquiv.trans
    (Ideal.quotEquivOfEq (divisorFiber_local_ideal_eq_power p Q))

omit [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S] [FaithfulSMul R S] in
/-- The indexing set of the product is finite. -/
theorem divisorFiber_product_finite (p : HeightOnePrime R) :
    Finite (PrimeSpectrum (p.1.asIdeal.Fiber S)) := inferInstance

omit [IsDomain R] in
/-- Every displayed factor in the fiber product is Artinian. -/
theorem divisorFiber_factor_artinian (p : HeightOnePrime R)
    (Q : HeightOnePrime S) [Q.1.asIdeal.LiesOver p.1.asIdeal] :
    IsArtinianRing (Localization.AtPrime Q.1.asIdeal ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime Q.1.asIdeal) ^
        heightOneRamificationIdx (R := R) Q) := by
  rw [← divisorFiber_local_ideal_eq_power p Q]
  infer_instance

omit [IsDomain R] [IsNoetherianRing R] [IsNoetherianRing S]
  [IsDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S] [FaithfulSMul R S] in
/-- Each local factor is a nonzero local ring as well as being Artinian. -/
theorem divisorFiber_factor_local (p : HeightOnePrime R)
    (Q : HeightOnePrime S) [Q.1.asIdeal.LiesOver p.1.asIdeal] :
    IsLocalRing (Localization.AtPrime Q.1.asIdeal ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime Q.1.asIdeal) ^
        heightOneRamificationIdx (R := R) Q) := by
  let Sq := Localization.AtPrime Q.1.asIdeal
  let I := IsLocalRing.maximalIdeal Sq ^ heightOneRamificationIdx (R := R) Q
  have hI : I ≠ ⊤ := by
    change ¬ IsLocalRing.maximalIdeal Sq ^ heightOneRamificationIdx (R := R) Q = ⊤
    rw [Ideal.pow_eq_top_iff]
    exact not_or.mpr ⟨(IsLocalRing.maximalIdeal.isMaximal Sq).ne_top,
      Nat.ne_of_gt (heightOneRamificationIdx_pos Q)⟩
  let : Nontrivial (Sq ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Reducedness of the actual fiber algebra is equivalent to all its
ramification indices being one. -/
theorem divisorFiber_reduced_iff (p : HeightOnePrime R) :
    _root_.IsReduced (p.1.asIdeal.Fiber S) ↔
      ∀ Q : p.1.asIdeal.primesOver S, Q.1.ramificationIdx R = 1 :=
  divisorFiber_isReduced_iff_forall_ramificationIdx_eq_one p

omit [IsNoetherianRing R] [IsNoetherianRing S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S] in
/-- Every point of the fiber corresponds to a height-one source prime, so
all factors are indexed by integral effective divisors over the target divisor. -/
theorem divisorFiber_factor_height_one (p : HeightOnePrime R)
    (q : PrimeSpectrum (p.1.asIdeal.Fiber S)) :
    (q.asIdeal.comap Algebra.TensorProduct.includeRight).height = 1 :=
  height_eq_one_of_liesOver_heightOne _ p.1.asIdeal inferInstance p.2

/-- Scheme-level product presentation for an affine map, using the intrinsic
scheme-theoretic fiber and `Spec` of the displayed product of local quotients. -/
def affine_generic_divisor_fiber_product_iso (p : HeightOnePrime R) :
    (Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiber p.1 ≅
      Spec (.of (∀ q : PrimeSpectrum (p.1.asIdeal.Fiber S),
        Localization.AtPrime (q.asIdeal.comap Algebra.TensorProduct.includeRight) ⧸
          IsLocalRing.maximalIdeal
            (Localization.AtPrime (q.asIdeal.comap Algebra.TensorProduct.includeRight)) ^
              (q.asIdeal.comap Algebra.TensorProduct.includeRight).ramificationIdx R)) :=
  (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R S p.1)) ≪≫
    Scheme.Spec.mapIso (divisorFiber_product_equiv p).toCommRingCatIso.symm.op

end Rings

/-- Product presentation of the intrinsic fiber of an arbitrary scheme map.
Any affine neighborhood of the target divisor may be used; finite preimage
supplies the affine source chart. The factors are the canonical affine
localizations, representing the local rings of the source at those divisors. -/
def generic_divisor_fiber_product_iso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] (E : SchemeDivisorPoint Y)
    (U : Y.affineOpens) (hE : E.1 ∈ (U : Y.Opens)) :
    let R := Γ(Y, U)
    let S := Γ(X, finitePreimageAffine f U)
    letI : Algebra R S := (f.app U).hom.toAlgebra
    let p := affinePrimeOfSchemeDivisorPoint E U hE
    f.fiber E.1 ≅ Spec (.of (divisorFiberProductRing (S := S) p)) := by
  let V := finitePreimageAffine f U
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let p := affinePrimeOfSchemeDivisorPoint E U hE
  let y : (U : Y.Opens).toScheme := ⟨E.1, hE⟩
  let x : X := Function.surjInv f.surjective E.1
  have hfx : f x = E.1 := Function.surjInv_eq f.surjective E.1
  have hxV : x ∈ (V : X.Opens) := by
    change f x ∈ (U : Y.Opens)
    rwa [hfx]
  letI : Nonempty (U : Y.Opens) := ⟨y⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨x, hxV⟩⟩
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  have hp : p.1 = U.2.primeIdealOf y := by
    apply PrimeSpectrum.ext
    exact pointClosureIdealSheaf_ideal E.1 U hE
  have emap :
      (Spec.map (f.appLE U V le_rfl)).fiber (U.2.primeIdealOf y) =
        (Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiber p.1 := by
    rw [hp]
    congr 2
    exact f.appLE_eq_app
  exact (schemeFiberRestrictIso f (U : Y.Opens) y).symm ≪≫
    finiteRestrictFiberIsoSpec f U y ≪≫ eqToIso emap ≪≫
      affine_generic_divisor_fiber_product_iso p

/-- Every intrinsic generic-divisor fiber has the displayed local quotient
product presentation. The affine neighborhood is chosen in the conclusion,
not imposed as an additional hypothesis. -/
theorem exists_generic_divisor_fiber_product_iso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] (E : SchemeDivisorPoint Y) :
    ∃ (U : Y.affineOpens) (hE : E.1 ∈ (U : Y.Opens)),
      let S := Γ(X, finitePreimageAffine f U)
      letI : Algebra Γ(Y, U) S := (f.app U).hom.toAlgebra
      Nonempty (f.fiber E.1 ≅ Spec (.of
        (divisorFiberProductRing (S := S) (affinePrimeOfSchemeDivisorPoint E U hE)))) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hEW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ E.1) isOpen_univ
  exact ⟨⟨W, hW⟩, hEW, ⟨generic_divisor_fiber_product_iso f E ⟨W, hW⟩ hEW⟩⟩

/-- Intrinsic scheme formulation: the fiber at the generic point of an
integral effective divisor is reduced iff every divisor above it has index one. -/
theorem generic_divisor_fiber_reduced_iff
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] (E : SchemeDivisorPoint Y) :
    AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      ∀ D : SchemeDivisorPoint X, f D.1 = E.1 → schemeDivisorRamificationIdx f D = 1 :=
  schemeDivisorFiber_isReduced_iff_forall_schemeDivisorRamificationIdx_eq_one f E

/-- The branch criterion uses the actual scheme fiber, not an assumed model. -/
theorem generic_divisor_fiber_nonreduced_iff
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] (E : SchemeDivisorPoint Y) :
    ¬ AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      ∃ D : SchemeDivisorPoint X, f D.1 = E.1 ∧ 1 < schemeDivisorRamificationIdx f D :=
  mem_schemeReducedFiberBranch_iff f E

/-- The union of branch divisors defined by ramification equals the union
defined by nonreduced actual fibers. This is the branch description used before
pushing forward along the target normalization. -/
theorem branch_support_eq_nonreduced_fiber_support
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    divisorSupport {E : SchemeDivisorPoint Y | ∃ D : SchemeDivisorPoint X,
      f D.1 = E.1 ∧ 1 < schemeDivisorRamificationIdx f D} =
      divisorSupport {E : SchemeDivisorPoint Y | ¬ AlgebraicGeometry.IsReduced (f.fiber E.1)} := by
  congr 1
  ext E
  exact (generic_divisor_fiber_nonreduced_iff f E).symm

/-- The normalized branch support is the target-normalization image of
exactly the divisors with nonreduced fibers upstairs. Equivalently it is the
image of the ramification-index branch support. All normalization finiteness
is derived from the varieties' structure maps. -/
theorem normalized_branch_support_eq_image_ramified_support
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    normalizedMorphismBranchSupport f =
      Palomar.normalizationMap Y '' divisorSupport
        {E : SchemeDivisorPoint (Palomar.normalization Y) |
          ∃ D : SchemeDivisorPoint (Palomar.normalization X),
            schemeGlobalNormalizationMorphism f D.1 = E.1 ∧
              1 < schemeDivisorRamificationIdx (schemeGlobalNormalizationMorphism f) D} := by
  let : IsFinite (Palomar.normalizationMap Y) := schemeGlobalNormalizationMap_isFinite Y k sY
  let : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Y ≫ sY)
  obtain ⟨hfinite, hsurj, -⟩ := canonical_normalization_lift_finite_surjective k sX f
  let : IsFinite (schemeGlobalNormalizationMorphism f) := hfinite
  let : Surjective (schemeGlobalNormalizationMorphism f) := ⟨hsurj⟩
  unfold normalizedMorphismBranchSupport
  rw [branch_support_eq_nonreduced_fiber_support (schemeGlobalNormalizationMorphism f)]
  rfl

end

end Pcf.PaperCharZero
