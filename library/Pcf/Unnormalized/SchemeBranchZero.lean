/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeBranch
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Pcf.Stacks.Purity.Tag0BMBScheme

/-!
# The local algebra criterion for the unnormalized branch locus

This proves `paper-p.tex`, Lemma `lem:branch-crit`, case `i = 0` for actual
finite dominant maps of integral varieties over a characteristic-zero field.
The affine finite-fiber criterion is transported through the intrinsic scheme
fiber and the original map's stalks. No normality hypothesis is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf

universe u

set_option linter.style.haveILetI false

/-- For an essentially finite type local homomorphism with Artinian closed
fiber and separable residue extension, the closed fiber is reduced precisely
when the homomorphism is formally unramified. This is the local algebra
criterion used in `paper-p.tex`, Lemma `lem:branch-crit`, case `i = 0`. -/
theorem localFiber_isReduced_iff_formallyUnramified
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    [IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))] :
    IsReduced (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) ↔
      Algebra.FormallyUnramified R S := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hI : I ≤ IsLocalRing.maximalIdeal S :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 1 3 rfl rfl).mp inferInstance
  letI : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hI)
  letI : IsLocalRing (S ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  constructor
  · intro hred
    letI : IsReduced (S ⧸ I) := hred
    have hfield : IsField (S ⧸ I) :=
      IsArtinianRing.isField_of_isReduced_of_isLocalRing _
    have heq : I = IsLocalRing.maximalIdeal S := by
      apply IsLocalRing.eq_maximalIdeal
      rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
      exact hfield
    exact Algebra.FormallyUnramified.of_map_maximalIdeal heq
  · intro hunr
    letI : Algebra.FormallyUnramified R S := hunr
    have hfield : IsField (S ⧸ I) :=
      Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal
    letI := hfield.toField
    infer_instance

/-- Characteristic-zero form of the local fiber criterion. Separability is
supplied by the residue field rather than taken as a geometric hypothesis.
The Artinian hypothesis is the algebraic finiteness property of a finite
scheme fiber; transporting that property from an actual scheme map is a
separate obligation. -/
theorem localFiber_isReduced_iff_formallyUnramified_charZero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S]
    [CharZero (IsLocalRing.ResidueField R)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    [IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))] :
    IsReduced (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) ↔
      Algebra.FormallyUnramified R S :=
  localFiber_isReduced_iff_formallyUnramified

/-- A finite algebra over a characteristic-zero field is reduced exactly
when it is formally unramified. This supplies the reduced-fiber criterion
without a normality hypothesis at the level of the whole affine fiber. -/
theorem finiteAlgebra_isReduced_iff_formallyUnramified_charZero
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Module.Finite K A] :
    IsReduced A ↔ Algebra.FormallyUnramified K A := by
  constructor
  · intro hred
    letI : IsReduced A := hred
    letI : IsArtinianRing A := isArtinian_of_tower K inferInstance
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    let L := Localization.AtPrime q.asIdeal
    letI : IsArtinianRing L :=
      IsArtinianRing.localization_artinian q.asIdeal.primeCompl L
    have hfield : IsField L := IsArtinianRing.isField_of_isReduced_of_isLocalRing L
    letI := hfield.toField
    letI : Module.Finite K L := Module.Finite.of_surjective
      (IsScalarTower.toAlgHom K A L).toLinearMap
      (IsArtinianRing.localization_surjective q.asIdeal.primeCompl L)
    exact Algebra.FormallyUnramified.of_isSeparable K L
  · intro hunr
    letI : Algebra.FormallyUnramified K A := hunr
    exact Algebra.FormallyUnramified.isReduced_of_field K A

open AlgebraicGeometry CategoryTheory in
/-- A finite map of affine schemes whose target section ring is a field of
characteristic zero has reduced source exactly when it is formally unramified.
This applies to finite scheme fibers once their residue-field target is
identified with its ring of global sections. -/
theorem finiteAffine_isReduced_iff_formallyUnramified_charZero
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [IsAffine X] [IsAffine Y]
    [CharZero Γ(Y, ⊤)] (hY : IsField Γ(Y, ⊤)) :
    AlgebraicGeometry.IsReduced X ↔ AlgebraicGeometry.FormallyUnramified f := by
  letI := hY.toField
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  rw [HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.FormallyUnramified)]
  change AlgebraicGeometry.IsReduced X ↔ Algebra.FormallyUnramified Γ(Y, ⊤) Γ(X, ⊤)
  rw [← finiteAlgebra_isReduced_iff_formallyUnramified_charZero Γ(Y, ⊤) Γ(X, ⊤)]
  exact ⟨fun _ => inferInstance, fun _ => isReduced_of_isAffine_isReduced X⟩

open AlgebraicGeometry CategoryTheory in
/-- The actual intrinsic fiber of a finite scheme morphism is reduced
exactly when its structure map to the target residue field is formally
unramified, in characteristic zero. No normality or integrality is needed.
This is a statement about the fiber structure map, not yet about the stalk
maps of the original morphism. -/
theorem finiteSchemeFiber_isReduced_iff_formallyUnramified_charZero
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] (y : Y)
    [CharZero (Y.residueField y)] :
    AlgebraicGeometry.IsReduced (f.fiber y) ↔
      AlgebraicGeometry.FormallyUnramified (f.fiberToSpecResidueField y) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y))).commRingCatIsoToRingEquiv
  letI : CharZero Γ(Spec (CommRingCat.of (Y.residueField y)), ⊤) :=
    (RingHom.charZero_iff e.injective).mpr inferInstance
  have hfield : IsField Γ(Spec (CommRingCat.of (Y.residueField y)), ⊤) :=
    e.toMulEquiv.isField (Field.toIsField _)
  exact finiteAffine_isReduced_iff_formallyUnramified_charZero
    (f.fiberToSpecResidueField y) hfield

section FiniteFiber
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
variable (p : Ideal R) [p.IsPrime] [CharZero p.ResidueField]

/-- For a finite algebra, a characteristic-zero fiber is reduced exactly when
every prime over its base point is unramified. This is the affine local
criterion used in `paper-p.tex`, Lemma `lem:branch-crit`, case `i = 0`. -/
theorem finiteFiber_isReduced_iff_forall_unramifiedAt_charZero :
    IsReduced (p.Fiber S) ↔
      ∀ Q : p.primesOver S, Algebra.IsUnramifiedAt R Q.1 := by
  classical
  constructor
  · intro hred Q
    letI : IsReduced (p.Fiber S) := hred
    let q : PrimeSpectrum (p.Fiber S) :=
      PrimeSpectrum.primesOverOrderIsoFiber R S p Q
    let r : Ideal S := q.asIdeal.comap Algebra.TensorProduct.includeRight
    have hr : r = Q.1 := by
      change ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm q).1 = Q.1
      exact congrArg Subtype.val
        ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply Q)
    letI : r.IsPrime := inferInstance
    letI : r.LiesOver p := inferInstance
    letI := Localization.AtPrime.algebraOfLiesOver p r
    let e := Ideal.Fiber.localizationAlgEquivQuotient p q.asIdeal
    have hloc : IsReduced (Localization.AtPrime q.asIdeal) := inferInstance
    have hquot : IsReduced
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) :=
      isReduced_of_injective e.symm e.symm.injective
    letI : IsReduced
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) := hquot
    have hIle : p.map (algebraMap R (Localization.AtPrime r)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime r) := by
      have hloc : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime r)) ≤
            IsLocalRing.maximalIdeal (Localization.AtPrime r) :=
        ((IsLocalRing.local_hom_TFAE
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime r))).out
          1 3 rfl rfl).mp inferInstance
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map] at hloc
      convert hloc using 1
      congr 1
      exact IsScalarTower.algebraMap_eq R (Localization.AtPrime p)
        (Localization.AtPrime r)
    letI : Nontrivial
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hIle)
    letI : IsLocalRing
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) :=
      .of_surjective' _ Ideal.Quotient.mk_surjective
    have hfield : IsField
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) :=
      IsArtinianRing.isField_of_isReduced_of_isLocalRing _
    have heq : p.map (algebraMap R (Localization.AtPrime r)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime r) := by
      apply IsLocalRing.eq_maximalIdeal
      rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
      exact hfield
    have hsep : Algebra.IsSeparable p.ResidueField r.ResidueField := inferInstance
    have hu : Algebra.IsUnramifiedAt R r :=
      (Algebra.isUnramifiedAt_iff_map_eq R p r).mpr ⟨hsep, heq⟩
    simpa only [hr] using hu
  · intro h
    apply isReduced_ofLocalizationMaximal
    intro q hq
    letI : q.IsPrime := hq.isPrime
    let Q : p.primesOver S :=
      (PrimeSpectrum.primesOverOrderIsoFiber R S p).symm ⟨q, inferInstance⟩
    let r : Ideal S := q.comap Algebra.TensorProduct.includeRight
    have hr : r = Q.1 := by
      change ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm ⟨q, inferInstance⟩).1 = Q.1
      rfl
    letI : r.IsPrime := inferInstance
    letI : r.LiesOver p := inferInstance
    letI := Localization.AtPrime.algebraOfLiesOver p r
    let e := Ideal.Fiber.localizationAlgEquivQuotient p q
    have hu : Algebra.IsUnramifiedAt R r := by simpa only [hr] using h Q
    have heq : p.map (algebraMap R (Localization.AtPrime r)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime r) :=
      (Algebra.isUnramifiedAt_iff_map_eq R p r).mp hu |>.2
    have hfield : IsField
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) := by
      rw [heq]
      exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
    letI := hfield.toField
    have hquot : IsReduced
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) := inferInstance
    exact isReduced_of_injective e e.injective

end FiniteFiber

/-- The intrinsic fiber of a finite map, restricted to an affine target chart,
is reduced exactly when each corresponding affine prime is unramified.
No normality is assumed. -/
theorem schemeDivisorFiber_isReduced_iff_forall_chart_unramifiedAt_charZero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    (U : Y.affineOpens) (E : SchemeDivisorPoint Y)
    (hE : E.1 ∈ (U : Y.Opens)) :
    AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      let p := affinePrimeOfSchemeDivisorPoint E U hE
      let S := Γ(X, finitePreimageAffine f U)
      letI : Algebra Γ(Y, U) S := (f.app U).hom.toAlgebra
      ∀ Q : p.1.asIdeal.primesOver S,
        Algebra.IsUnramifiedAt Γ(Y, U) Q.1 := by
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
  letI : Algebra k R := inferInstance
  letI : Algebra k p.1.asIdeal.ResidueField :=
    ((algebraMap R p.1.asIdeal.ResidueField).comp (algebraMap k R)).toAlgebra
  letI : CharZero p.1.asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap k p.1.asIdeal.ResidueField).injective
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
  dsimp only
  let e := Spec.fiberToSpecResidueFieldIso R S p.1
  constructor
  · intro hred
    have hspec' : AlgebraicGeometry.IsReduced (Spec (.of (p.1.asIdeal.Fiber S))) :=
      @isReduced_of_isOpenImmersion _ _ e.inv.left inferInstance hred
    have hring : IsReduced (p.1.asIdeal.Fiber S) := (affine_isReduced_iff _).mp hspec'
    exact (finiteFiber_isReduced_iff_forall_unramifiedAt_charZero
      (R := R) (S := S) p.1.asIdeal).mp hring
  · intro h
    have hring : IsReduced (p.1.asIdeal.Fiber S) :=
      (finiteFiber_isReduced_iff_forall_unramifiedAt_charZero
        (R := R) (S := S) p.1.asIdeal).mpr h
    letI : IsReduced (p.1.asIdeal.Fiber S) := hring
    have hspec' : AlgebraicGeometry.IsReduced (Spec (.of (p.1.asIdeal.Fiber S))) :=
      (affine_isReduced_iff _).mpr hring
    exact @isReduced_of_isOpenImmersion _ _ e.hom.left inferInstance hspec'


/-- The intrinsic fiber over a target divisor is reduced exactly when the
original finite map is formally unramified at every source divisor above it.
This is the stalk comparison in `paper-p.tex`, Lemma `lem:branch-crit`,
case `i = 0`, without normality. -/
theorem schemeDivisorFiber_isReduced_iff_forall_stalkUnramified_charZero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    (E : SchemeDivisorPoint Y) :
    AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      ∀ P : SchemeDivisorPoint X, f P.1 = E.1 →
        (f.stalkMap P.1).hom.FormallyUnramified := by
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
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  have hchart (q : PrimeSpectrum S) :
      U.2.fromSpec (PrimeSpectrum.comap (f.app U).hom q) =
        f (V.2.fromSpec q) := by
    have h := congrArg (fun g : Spec S ⟶ Y => g q)
      (IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 le_rfl)
    change U.2.fromSpec
      (PrimeSpectrum.comap (f.appLE U V le_rfl).hom q) =
        f (V.2.fromSpec q) at h
    have happ : f.appLE U V le_rfl = f.app U := f.appLE_eq_app
    rwa [happ] at h
  have hpback : U.2.fromSpec p.1 = E.1 :=
    congrArg Subtype.val (schemeDivisorPointOfAffinePrime_affinePrime E U hEW)
  rw [schemeDivisorFiber_isReduced_iff_forall_chart_unramifiedAt_charZero f k U E hEW]
  dsimp only
  constructor
  · intro hram P hPE
    have hPV : P.1 ∈ (V : X.Opens) := by
      change f P.1 ∈ (U : Y.Opens)
      rwa [hPE]
    let q := affinePrimeOfSchemeDivisorPoint P V hPV
    have hq_rec : schemeDivisorPointOfAffinePrime V q = P :=
      schemeDivisorPointOfAffinePrime_affinePrime P V hPV
    have hqback : V.2.fromSpec q.1 = P.1 := congrArg Subtype.val hq_rec
    have hq_under : PrimeSpectrum.comap (f.app U).hom q.1 = p.1 :=
      (show Function.Injective U.2.fromSpec from by
        let hU : IsAffineOpen (U : Y.Opens) := U.2
        exact hU.fromSpec.isEmbedding.injective) (by
        rw [hchart, hqback, hPE, hpback])
    have hq_lies : q.1.asIdeal.LiesOver p.1.asIdeal := by
      constructor
      exact congrArg PrimeSpectrum.asIdeal hq_under |>.symm
    let qOver : p.1.asIdeal.primesOver S :=
      ⟨q.1.asIdeal, inferInstance, hq_lies⟩
    have hq : Algebra.IsUnramifiedAt R q.1.asIdeal := hram qOver
    have hq_id : q.1 = V.2.primeIdealOf ⟨P.1, hPV⟩ := by
      apply PrimeSpectrum.ext
      exact pointClosureIdealSheaf_ideal P.1 V hPV
    have happ : f.appLE U V le_rfl = f.app U := f.appLE_eq_app
    have hiff := Pcf.Stacks.formallyUnramified_stalkMap_iff
      (f := f) (x := P.1) (U : Y.Opens) U.2 (V : X.Opens) V.2 le_rfl hPV
    have hq' : @Algebra.IsUnramifiedAt R S inferInstance inferInstance
        (f.appLE U V le_rfl).hom.toAlgebra
        (V.2.primeIdealOf ⟨P.1, hPV⟩).asIdeal inferInstance := by
      rw [happ, ← hq_id]
      exact hq
    exact hiff.mpr hq'
  · intro hram Q
    let qIdeal : Ideal S := Q.1
    letI : qIdeal.IsPrime := Q.2.1
    letI : qIdeal.LiesOver p.1.asIdeal := Q.2.2
    have hqheight : qIdeal.height = 1 :=
      height_eq_one_of_liesOver_heightOne qIdeal p.1.asIdeal inferInstance p.2
    let q : HeightOnePrime S := ⟨⟨qIdeal, inferInstance⟩, hqheight⟩
    let D := schemeDivisorPointOfAffinePrime V q
    have hmap : f D.1 = E.1 := by
      have hq_under : PrimeSpectrum.comap (f.app U).hom q.1 = p.1 := by
        apply PrimeSpectrum.ext
        exact (Ideal.LiesOver.over (p := p.1.asIdeal) (P := qIdeal)).symm
      change f (V.2.fromSpec q.1) = E.1
      rw [← hchart q.1, hq_under, hpback]
    have hD := hram D hmap
    have hDV : D.1 ∈ (V : X.Opens) := by
      change V.2.fromSpec q.1 ∈ (V : X.Opens)
      rw [← SetLike.mem_coe, ← V.2.range_fromSpec]
      exact Set.mem_range_self q.1
    have hq_id : V.2.primeIdealOf ⟨D.1, hDV⟩ = q.1 := by
      let hV : IsAffineOpen (V : X.Opens) := V.2
      apply hV.fromSpec.isEmbedding.injective
      rw [V.2.fromSpec_primeIdealOf]
      change D.1 = V.2.fromSpec q.1
      rfl
    have happ : f.appLE U V le_rfl = f.app U := f.appLE_eq_app
    have hiff := Pcf.Stacks.formallyUnramified_stalkMap_iff
      (f := f) (x := D.1) (U : Y.Opens) U.2 (V : X.Opens) V.2 le_rfl hDV
    have hq : Algebra.IsUnramifiedAt R qIdeal := by
      have hq' : @Algebra.IsUnramifiedAt R S inferInstance inferInstance
          (f.appLE U V le_rfl).hom.toAlgebra qIdeal inferInstance := by
        have hqraw := hiff.mp hD
        rw [hq_id] at hqraw
        exact hqraw
      rw [happ] at hq'
      exact hq'
    exact hq

/-- `paper-p.tex`, Lemma `lem:branch-crit`, case `i = 0`: a target
integral effective divisor has nonreduced fiber precisely when a source
integral effective divisor above it is non-unramified at its generic point. -/
theorem mem_schemeUnnormalizedBranchZero_iff_critical_divisor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    (E : SchemeDivisorPoint Y) :
    E ∈ schemeUnnormalizedBranchZero g ↔
      ∃ P : SchemeDivisorPoint X,
        g P.1 = E.1 ∧ P ∈ schemeUnnormalizedCriticalZero g := by
  change ¬ AlgebraicGeometry.IsReduced (g.fiber E.1) ↔ _
  rw [schemeDivisorFiber_isReduced_iff_forall_stalkUnramified_charZero g k E]
  push Not
  rfl

/-- Set-level image form of `paper-p.tex`, Lemma `lem:branch-crit`, case
`i = 0`, using the canonical finite-map pushforward of divisors.

`paper-p.tex` correspondence: Lemma A.3 (`lem:branch-crit`). -/
theorem schemeUnnormalizedBranchZero_eq_image_critical
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)] :
    schemeUnnormalizedBranchZero g =
      (fun P : SchemeDivisorPoint X => P.mapFiniteDominantFiniteType g k) ''
        schemeUnnormalizedCriticalZero g := by
  ext E
  rw [mem_schemeUnnormalizedBranchZero_iff_critical_divisor g k E]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨P, hP, hcrit⟩
    exact ⟨P, hcrit, Subtype.ext hP⟩
  · rintro ⟨P, hcrit, hP⟩
    exact ⟨P, congrArg Subtype.val hP, hcrit⟩


#print axioms schemeDivisorFiber_isReduced_iff_forall_stalkUnramified_charZero
#print axioms mem_schemeUnnormalizedBranchZero_iff_critical_divisor
#print axioms schemeUnnormalizedBranchZero_eq_image_critical
#print axioms finiteFiber_isReduced_iff_forall_unramifiedAt_charZero
#print axioms schemeDivisorFiber_isReduced_iff_forall_chart_unramifiedAt_charZero
#print axioms localFiber_isReduced_iff_formallyUnramified
#print axioms localFiber_isReduced_iff_formallyUnramified_charZero
#print axioms finiteAlgebra_isReduced_iff_formallyUnramified_charZero
#print axioms finiteAffine_isReduced_iff_formallyUnramified_charZero
#print axioms finiteSchemeFiber_isReduced_iff_formallyUnramified_charZero

end Pcf
