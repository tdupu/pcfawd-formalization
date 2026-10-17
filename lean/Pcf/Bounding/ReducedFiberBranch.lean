/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AffineSchemeRamification
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Reduced divisor fibers and ramification indices

This file identifies the manuscript's scheme-theoretic reduced-fiber definition
of the branch locus with the ramification-index definition already used by the
divisor dynamics.  The comparison is first proved for finite extensions of
normal Noetherian domains, then transported through affine charts to the
intrinsic scheme fiber `f.fiber E`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

universe u

set_option linter.style.haveILetI false

/-- The local fiber at a height-one source prime is reduced exactly when its
ramification index is one. -/
theorem localDivisorFiber_isReduced_iff_ramificationIdx_eq_one
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (p : HeightOnePrime R) (Q : HeightOnePrime S)
    [Q.1.asIdeal.LiesOver p.1.asIdeal] :
    _root_.IsReduced
      (Localization.AtPrime Q.1.asIdeal ⧸
        p.1.asIdeal.map (algebraMap R (Localization.AtPrime Q.1.asIdeal))) ↔
      heightOneRamificationIdx (R := R) Q = 1 := by
  let Sq := Localization.AtPrime Q.1.asIdeal
  let m := IsLocalRing.maximalIdeal Sq
  letI : IsDiscreteValuationRing Sq :=
    heightOnePrime_localRing_isDiscreteValuationRing Q
  have hpow : p.1.asIdeal.map (algebraMap R Sq) =
      m ^ heightOneRamificationIdx (R := R) Q := by
    rw [heightOneRamificationIdx_eq_dvrExponent (R := R) Q]
    simpa only [show Q.1.asIdeal.under R = p.1.asIdeal from
      (Ideal.LiesOver.over (p := p.1.asIdeal) (P := Q.1.asIdeal)).symm] using
      heightOneDvrExponent_spec (R := R) Q
  rw [← Ideal.isRadical_iff_quotient_reduced, hpow]
  constructor
  · intro hrad
    have hpos : 0 < heightOneRamificationIdx (R := R) Q := heightOneRamificationIdx_pos Q
    have heq : m ^ heightOneRamificationIdx (R := R) Q = m := by
      rw [← hrad.radical, Ideal.radical_pow m (Nat.ne_of_gt hpos)]
      exact (inferInstance : m.IsPrime).radical
    have hcoheight := congrArg Order.coheight heq
    have hleft : Order.coheight (m ^ heightOneRamificationIdx (R := R) Q) =
        (heightOneRamificationIdx (R := R) Q : ℕ∞) := by
      dsimp [m]
      rw [IsDiscreteValuationRing.coheight_pow_maximalIdeal]
    have hright : Order.coheight m = (1 : ℕ∞) := by
      rw [← pow_one m]
      dsimp [m]
      rw [IsDiscreteValuationRing.coheight_pow_maximalIdeal]
      norm_num
    have hcoe : (heightOneRamificationIdx (R := R) Q : ℕ∞) = (1 : ℕ∞) :=
      hleft.symm.trans (hcoheight.trans hright)
    exact_mod_cast hcoe
  · intro he
    rw [he, pow_one]
    exact (inferInstance : m.IsPrime).isRadical

/-- Localizing the whole fiber at one of its primes gives the corresponding
height-one local fiber. -/
theorem localizationFiber_isReduced_iff_ramificationIdx_eq_one
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (p : HeightOnePrime R) (q : Ideal (p.1.asIdeal.Fiber S)) [q.IsPrime] :
    _root_.IsReduced (Localization.AtPrime q) ↔
      (q.comap Algebra.TensorProduct.includeRight).ramificationIdx R = 1 := by
  let r : Ideal S := q.comap Algebra.TensorProduct.includeRight
  letI : r.IsPrime := (inferInstance : q.IsPrime).comap
    Algebra.TensorProduct.includeRight
  letI : r.LiesOver p.1.asIdeal := inferInstance
  have hrheight : r.height = 1 :=
    height_eq_one_of_liesOver_heightOne r p.1.asIdeal inferInstance p.2
  let Q : HeightOnePrime S := ⟨⟨r, inferInstance⟩, hrheight⟩
  letI : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p.1.asIdeal r
  let e := Ideal.Fiber.localizationAlgEquivQuotient p.1.asIdeal q
  have hlocal := localDivisorFiber_isReduced_iff_ramificationIdx_eq_one
    (R := R) (S := S) p Q
  constructor
  · intro hred
    letI : _root_.IsReduced (Localization.AtPrime q) := hred
    have hquot : _root_.IsReduced
        (Localization.AtPrime r ⧸
          p.1.asIdeal.map (algebraMap R (Localization.AtPrime r))) :=
      isReduced_of_injective e.symm e.symm.injective
    exact hlocal.mp hquot
  · intro hram
    have hquot : _root_.IsReduced
        (Localization.AtPrime r ⧸
          p.1.asIdeal.map (algebraMap R (Localization.AtPrime r))) :=
      hlocal.mpr hram
    letI : _root_.IsReduced
        (Localization.AtPrime r ⧸
          p.1.asIdeal.map (algebraMap R (Localization.AtPrime r))) := hquot
    exact isReduced_of_injective e e.injective

/-- A height-one affine fiber is reduced exactly when every prime over the
target divisor has ramification index one. -/
theorem divisorFiber_isReduced_iff_forall_ramificationIdx_eq_one
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (p : HeightOnePrime R) :
    _root_.IsReduced (p.1.asIdeal.Fiber S) ↔
      ∀ Q : p.1.asIdeal.primesOver S, Q.1.ramificationIdx R = 1 := by
  constructor
  · intro hred Q
    letI : _root_.IsReduced (p.1.asIdeal.Fiber S) := hred
    let q : PrimeSpectrum (p.1.asIdeal.Fiber S) :=
      PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal Q
    have hlocal : _root_.IsReduced (Localization.AtPrime q.asIdeal) := inferInstance
    have hram := (localizationFiber_isReduced_iff_ramificationIdx_eq_one
      (R := R) (S := S) p q.asIdeal).mp hlocal
    have hr : q.asIdeal.comap Algebra.TensorProduct.includeRight = Q.1 := by
      change ((PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal).symm q).1 = Q.1
      exact congrArg Subtype.val
        ((PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal).symm_apply_apply Q)
    rw [hr] at hram
    exact hram
  · intro hram
    apply isReduced_ofLocalizationMaximal
    intro q hq
    letI : q.IsPrime := hq.isPrime
    apply (localizationFiber_isReduced_iff_ramificationIdx_eq_one
      (R := R) (S := S) p q).mpr
    let Q : p.1.asIdeal.primesOver S :=
      (PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal).symm ⟨q, inferInstance⟩
    have := hram Q
    simpa [Q, PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply] using this

/-- The preceding affine comparison expressed using Mathlib's intrinsic
scheme fiber of a map between affine schemes. -/
theorem affineSchemeDivisorFiber_isReduced_iff_forall_ramificationIdx_eq_one
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (p : HeightOnePrime R) :
    AlgebraicGeometry.IsReduced
        ((Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiber p.1) ↔
      ∀ Q : p.1.asIdeal.primesOver S, Q.1.ramificationIdx R = 1 := by
  let g := Spec.map (CommRingCat.ofHom <| algebraMap R S)
  let e := Spec.fiberToSpecResidueFieldIso R S p.1
  constructor
  · intro hred
    letI : AlgebraicGeometry.IsReduced (g.fiber p.1) := hred
    have hspec : AlgebraicGeometry.IsReduced
        (Spec (.of (p.1.asIdeal.Fiber S))) :=
      @isReduced_of_isOpenImmersion _ _ e.inv.left inferInstance hred
    have hring : _root_.IsReduced (p.1.asIdeal.Fiber S) :=
      (affine_isReduced_iff _).mp hspec
    exact (divisorFiber_isReduced_iff_forall_ramificationIdx_eq_one p).mp hring
  · intro hred
    have hring : _root_.IsReduced (p.1.asIdeal.Fiber S) :=
      (divisorFiber_isReduced_iff_forall_ramificationIdx_eq_one p).mpr hred
    letI : _root_.IsReduced (p.1.asIdeal.Fiber S) := hring
    have hspec : AlgebraicGeometry.IsReduced
        (Spec (.of (p.1.asIdeal.Fiber S))) := (affine_isReduced_iff _).mpr hring
    letI : AlgebraicGeometry.IsReduced (Spec (.of (p.1.asIdeal.Fiber S))) := hspec
    exact @isReduced_of_isOpenImmersion _ _ e.hom.left inferInstance hspec

/-- Restricting a morphism over an open neighborhood of the target point does
not change its intrinsic scheme fiber. -/
noncomputable def schemeFiberRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (y : U.toScheme) :
    (f ∣_ U).fiber y ≅ f.fiber y.1 := by
  let V := f ⁻¹ᵁ U
  let g := f ∣_ U
  let a := U.toScheme.fromSpecResidueField y
  let b := Y.fromSpecResidueField y.1
  let h := Spec.map (U.ι.residueFieldMap y)
  letI : IsIso (U.ι.residueFieldMap y) := inferInstance
  letI hh : IsIso h := by
    dsimp [h]
    infer_instance
  have hcompat : h ≫ b = a ≫ U.ι := by
    dsimp [a, b, h]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι y
  let j := pullback.map g a f b V.ι h U.ι
    (by simp [g, V])
    hcompat.symm
  have Hres : IsPullback (pullback.fst g a) (pullback.snd g a) g a :=
    IsPullback.of_hasPullback g a
  have Hbase : IsPullback g V.ι U.ι f := by
    simpa [g, V] using isPullback_morphismRestrict f U
  have Houter : IsPullback (pullback.fst g a ≫ V.ι) (pullback.snd g a)
      f (h ≫ b) := by
    rw [hcompat]
    exact Hres.paste_horiz Hbase.flip
  have Hjcomm : j ≫ pullback.snd f b = pullback.snd g a ≫ h := by
    simp only [j, pullback.lift_snd]
    rfl
  have Hjfst : j ≫ pullback.fst f b = pullback.fst g a ≫ V.ι := by
    simp only [j, pullback.lift_fst]
  have Hj : IsPullback j (pullback.snd g a) (pullback.snd f b) h := by
    apply ((IsPullback.of_hasPullback f b).paste_horiz_iff Hjcomm).mp
    rw [Hjfst]
    exact Houter
  letI hj : IsIso j := Hj.isIso_fst_of_isIso hh
  exact @asIso Scheme _ _ _ j hj

theorem fiberRestrict_isReduced_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (y : U.toScheme) :
    AlgebraicGeometry.IsReduced ((f ∣_ U).fiber y) ↔
      AlgebraicGeometry.IsReduced (f.fiber y.1) := by
  let e := schemeFiberRestrictIso f U y
  constructor
  · intro hred
    exact @isReduced_of_isOpenImmersion _ _ e.inv inferInstance hred
  · intro hred
    exact @isReduced_of_isOpenImmersion _ _ e.hom inferInstance hred

/-- An isomorphism of arrows induces an isomorphism of the fibers at
corresponding target points. -/
noncomputable def schemeFiberIsoOfArrowIso
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (y : Y) :
    f.fiber y ≅ g.fiber (e.hom.right y) := by
  let a := Y.fromSpecResidueField y
  let b := Y'.fromSpecResidueField (e.hom.right y)
  let h := Spec.map (e.hom.right.residueFieldMap y)
  letI : IsOpenImmersion e.hom.right := inferInstance
  letI : IsIso (e.hom.right.residueFieldMap y) := inferInstance
  letI hh : IsIso h := by
    dsimp [h]
    infer_instance
  have hcompat : h ≫ b = a ≫ e.hom.right := by
    dsimp [a, b, h]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField e.hom.right y
  let j := pullback.map f a g b e.hom.left h e.hom.right e.hom.w.symm hcompat.symm
  letI hj : IsIso j := by
    dsimp [j]
    infer_instance
  exact @asIso Scheme _ _ _ j hj

/-- The restriction of a finite morphism over an affine target is the affine
map induced by its map on sections. -/
noncomputable def finiteRestrictArrowIsoSpec
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens) :
    Arrow.mk (f ∣_ (U : Y.Opens)) ≅
      Arrow.mk (Spec.map (f.appLE U (finitePreimageAffine f U) le_rfl)) := by
  let V := finitePreimageAffine f U
  refine Arrow.isoMk V.2.isoSpec U.2.isoSpec ?_
  simp only [Arrow.mk_hom]
  rw [V.2.isoSpec_hom, U.2.isoSpec_hom]
  dsimp only [V]
  simpa only [finitePreimageAffine_opens, Scheme.Hom.resLE_eq_morphismRestrict] using
    (Scheme.Opens.toSpecΓ_SpecMap_appLE f
      (U : Y.Opens) (finitePreimageAffine f U : X.Opens) le_rfl)

noncomputable def finiteRestrictFiberIsoSpec
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens)
    (y : (U : Y.Opens).toScheme) :
    (f ∣_ (U : Y.Opens)).fiber y ≅
      (Spec.map (f.appLE U (finitePreimageAffine f U) le_rfl)).fiber
        (U.2.primeIdealOf y) := by
  simpa [finiteRestrictArrowIsoSpec, IsAffineOpen.primeIdealOf] using
    (schemeFiberIsoOfArrowIso (finiteRestrictArrowIsoSpec f U) y)

/-- The intrinsic fiber at a divisor is reduced exactly when every prime over
its affine representative has ramification index one. -/
theorem schemeDivisorFiber_isReduced_iff_forall_chart_ramificationIdx_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (U : Y.affineOpens) (E : SchemeDivisorPoint Y)
    (hE : E.1 ∈ (U : Y.Opens)) :
    AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      let p := affinePrimeOfSchemeDivisorPoint E U hE
      let S := Γ(X, finitePreimageAffine f U)
      letI : Algebra Γ(Y, U) S := (f.app U).hom.toAlgebra
      ∀ Q : p.1.asIdeal.primesOver S,
        Q.1.ramificationIdx Γ(Y, U) = 1 := by
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
  have hp : p.1 = U.2.primeIdealOf y := by
    apply PrimeSpectrum.ext
    exact pointClosureIdealSheaf_ideal E.1 U hE
  have happ : f.appLE U V le_rfl = f.app U := f.appLE_eq_app
  have hspec : AlgebraicGeometry.IsReduced
        ((f ∣_ (U : Y.Opens)).fiber y) ↔
      AlgebraicGeometry.IsReduced
        ((Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiber p.1) := by
    let e := finiteRestrictFiberIsoSpec f U y
    have emap :
        (Spec.map (f.appLE U V le_rfl)).fiber (U.2.primeIdealOf y) =
          (Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiber p.1 := by
      rw [hp]
      congr 2
    rw [← emap]
    constructor
    · intro hred
      exact @isReduced_of_isOpenImmersion _ _ e.inv inferInstance hred
    · intro hred
      exact @isReduced_of_isOpenImmersion _ _ e.hom inferInstance hred
  rw [← fiberRestrict_isReduced_iff f (U : Y.Opens) y, hspec]
  exact affineSchemeDivisorFiber_isReduced_iff_forall_ramificationIdx_eq_one p

/-- Global form of the reduced-fiber criterion, quantified over actual
codimension-one points of the source scheme. -/
theorem schemeDivisorFiber_isReduced_iff_forall_schemeDivisorRamificationIdx_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (E : SchemeDivisorPoint Y) :
    AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      ∀ Q : SchemeDivisorPoint X, f Q.1 = E.1 → schemeDivisorRamificationIdx f Q = 1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hEW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ E.1) isOpen_univ
  let U : Y.affineOpens := ⟨W, hW⟩
  let V := finitePreimageAffine f U
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let p := affinePrimeOfSchemeDivisorPoint E U hEW
  let x : X := Function.surjInv f.surjective E.1
  have hfx : f x = E.1 := Function.surjInv_eq f.surjective E.1
  have hxV : x ∈ (V : X.Opens) := by
    change f x ∈ (U : Y.Opens)
    rwa [hfx]
  letI : Nonempty (U : Y.Opens) := ⟨⟨E.1, hEW⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨x, hxV⟩⟩
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  rw [schemeDivisorFiber_isReduced_iff_forall_chart_ramificationIdx_eq_one f U E hEW]
  dsimp only
  constructor
  · intro hram Q hQE
    have hQV : Q.1 ∈ (V : X.Opens) := by
      change f Q.1 ∈ (U : Y.Opens)
      rwa [hQE]
    let q := affinePrimeOfSchemeDivisorPoint Q V hQV
    have hq_rec : schemeDivisorPointOfAffinePrime V q = Q :=
      schemeDivisorPointOfAffinePrime_affinePrime Q V hQV
    have hq_under : heightOneUnder (R := R) q = p := by
      apply schemeDivisorPointOfAffinePrime_injective U
      rw [schemeDivisorPointOfAffinePrime_affinePrime E U hEW]
      apply Subtype.ext
      have hmap := schemeDivisorPointOfAffinePrime_map f U q
      rw [hq_rec] at hmap
      exact hmap.symm.trans hQE
    have hq_lies : q.1.asIdeal.LiesOver p.1.asIdeal := by
      constructor
      exact (congrArg (fun z : HeightOnePrime R ↦ z.1.asIdeal) hq_under).symm
    let qOver : p.1.asIdeal.primesOver S :=
      ⟨q.1.asIdeal, inferInstance, hq_lies⟩
    have h := hram qOver
    have h' : schemeDivisorRamificationIdx f
        (schemeDivisorPointOfAffinePrime V q) = 1 := by
      rw [schemeDivisorRamificationIdx_eq_heightOneRamificationIdx f U q]
      exact h
    rw [hq_rec] at h'
    exact h'
  · intro hram Q
    let qIdeal : Ideal S := Q.1
    letI : qIdeal.IsPrime := Q.2.1
    letI : qIdeal.LiesOver p.1.asIdeal := Q.2.2
    have hqheight : qIdeal.height = 1 :=
      height_eq_one_of_liesOver_heightOne qIdeal p.1.asIdeal inferInstance p.2
    let q : HeightOnePrime S := ⟨⟨qIdeal, inferInstance⟩, hqheight⟩
    let D := schemeDivisorPointOfAffinePrime V q
    have hmap : f D.1 = E.1 := by
      have hp_under : heightOneUnder (R := R) q = p := by
        apply Subtype.ext
        exact PrimeSpectrum.ext
          (Ideal.LiesOver.over (p := p.1.asIdeal) (P := qIdeal)).symm
      have hmap' := schemeDivisorPointOfAffinePrime_map f U q
      rw [hp_under] at hmap'
      exact hmap'.trans (congrArg Subtype.val
        (schemeDivisorPointOfAffinePrime_affinePrime E U hEW))
    have hD := hram D hmap
    rw [schemeDivisorRamificationIdx_eq_heightOneRamificationIdx f U q] at hD
    change qIdeal.ramificationIdx R = 1 at hD
    simpa only [qIdeal] using hD

/-- The codimension-one branch locus defined by nonreduced
scheme-theoretic fibers. -/
def schemeReducedFiberBranch {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set (SchemeDivisorPoint Y) :=
  {E | ¬ AlgebraicGeometry.IsReduced (f.fiber E.1)}

/-- For finite dominant maps of normal integral schemes, a divisor fiber is
nonreduced exactly when a divisor above it has ramification index greater
than one. -/
theorem mem_schemeReducedFiberBranch_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (E : SchemeDivisorPoint Y) :
    E ∈ schemeReducedFiberBranch f ↔
      ∃ Q : SchemeDivisorPoint X,
        f Q.1 = E.1 ∧ 1 < schemeDivisorRamificationIdx f Q := by
  rw [schemeReducedFiberBranch, Set.mem_ofPred_eq]
  constructor
  · intro hnonred
    have hnot : ¬ ∀ Q : SchemeDivisorPoint X,
        f Q.1 = E.1 → schemeDivisorRamificationIdx f Q = 1 := by
      intro h
      exact hnonred
        ((schemeDivisorFiber_isReduced_iff_forall_schemeDivisorRamificationIdx_eq_one f E).mpr h)
    push Not at hnot
    obtain ⟨Q, hQE, hne⟩ := hnot
    refine ⟨Q, hQE, ?_⟩
    have hpos := schemeDivisorRamificationIdx_pos f Q
    omega
  · rintro ⟨Q, hQE, hram⟩ hred
    have h :=
      (schemeDivisorFiber_isReduced_iff_forall_schemeDivisorRamificationIdx_eq_one f E).mp hred Q hQE
    omega

/-- On a normal scheme, the reduced-fiber branch definition is exactly the
ramification-index branch of the actual divisor dynamics. -/
theorem schemeReducedFiberBranch_eq_divisorDynamics_branch
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorNonEtaleLocus f).Finite) :
    schemeReducedFiberBranch f =
      (divisorDynamicsOfFiniteDominantNormal f hcrit).branch := by
  ext E
  rw [mem_schemeReducedFiberBranch_iff f E, DivisorDynamics.mem_branch_iff]
  constructor
  · rintro ⟨Q, hQE, hram⟩
    exact ⟨Q, Subtype.ext hQE, hram⟩
  · rintro ⟨Q, hQE, hram⟩
    exact ⟨Q, congrArg Subtype.val hQE, hram⟩

#print axioms localDivisorFiber_isReduced_iff_ramificationIdx_eq_one
#print axioms localizationFiber_isReduced_iff_ramificationIdx_eq_one
#print axioms divisorFiber_isReduced_iff_forall_ramificationIdx_eq_one
#print axioms affineSchemeDivisorFiber_isReduced_iff_forall_ramificationIdx_eq_one
#print axioms schemeFiberRestrictIso
#print axioms schemeFiberIsoOfArrowIso
#print axioms schemeDivisorFiber_isReduced_iff_forall_schemeDivisorRamificationIdx_eq_one
#print axioms schemeReducedFiberBranch
#print axioms mem_schemeReducedFiberBranch_iff
#print axioms schemeReducedFiberBranch_eq_divisorDynamics_branch

end

end Pcf
