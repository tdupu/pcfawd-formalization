/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.ReducedFiberBranch
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Scheme-level fibre decomposition over a divisor (`paper-p.tex`, l. 364–371)

The source: for a finite dominant map `g̃ : Ã → B̃` of normal varieties and an
integral divisor `Ẽ` of `B̃`, "the fibre of `g̃` over the generic point of `Ẽ` is
`∏_{D̃} 𝒪_{Ã,D̃}/𝔪_{D̃}^{e(D̃/Ẽ)}`, the product over the divisors `D̃` over `Ẽ`",
and "it is reduced exactly when all divisors above it have ramification index one".

This file states this for the actual morphism `f : X ⟶ Y` (finite, dominant,
`X`, `Y` normal integral, `Y` locally Noetherian) and its Mathlib scheme fibre
`f.fiber E` at a codimension-one point `E`:

* `schemeFiberΓEquivPi`: `Γ(f.fiber E, ⊤) ≃+* Π D, 𝒪_{X,D} ⧸ 𝔪_D ^ e(D)`, the
  product over `SchemeDivisorPointsOver f E = {D : SchemeDivisorPoint X // f D = E}`,
  with `e = schemeDivisorRamificationIdx f` (the actual stalk ramification index).
* `schemeFiberIsoSpecChartFiber`: the fibre scheme is affine, isomorphic to `Spec`
  of the chart fibre ring, so its global sections determine it.
* `schemeFiber_isReduced_iff_forall_divisorsOver`,
  `schemeFiberΓ_isReduced_iff_forall_divisorsOver`: the reducedness criterion.

Route: on an affine chart `U ∋ E` with finite preimage chart `V`, `S = Γ(X, V)`
is finite over `R = Γ(Y, U)` and `f.fiber E ≅ Spec (κ(p) ⊗_R S)`. The fibre ring is
Artinian, hence the product of its localizations (Stacks 00JA, in Mathlib); the
localization at a prime `q` is `S_Q / p S_Q = S_Q / 𝔪_Q^e` with `Q` the height-one
prime of `S` under `q`, and `S_Q` is the stalk of `X` at the corresponding divisor.

Divergences from the manuscript: the manuscript's "fibre" is read as the ring of
global sections of the affine scheme `f.fiber E` (the scheme itself is identified
by `schemeFiberIsoSpecChartFiber`). The chart route replaces the manuscript's base
change to `Spec 𝒪_{B̃,Ẽ}`; the two agree since `κ(p) ⊗_R S = κ(p) ⊗_{R_p} S_p`.
The exponent is Mathlib's length ramification index, equal to the DVR exponent
(`heightOneRamificationIdx_eq_dvrExponent`). No separability hypothesis is used.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

universe u

set_option linter.style.haveILetI false

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]

/-- The prime of `S` under a prime of the fibre ring, as a height-one prime. -/
def fibrePrimeHeightOne (p : HeightOnePrime R) (q : PrimeSpectrum (p.1.asIdeal.Fiber S)) :
    HeightOnePrime S :=
  letI : (q.asIdeal.comap Algebra.TensorProduct.includeRight).IsPrime :=
    q.2.comap Algebra.TensorProduct.includeRight
  ⟨⟨q.asIdeal.comap Algebra.TensorProduct.includeRight, inferInstance⟩,
    height_eq_one_of_liesOver_heightOne _ p.1.asIdeal inferInstance p.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The local factor of the fibre at one of its primes `q`: the localization
of the fibre at `q` is `S_Q / 𝔪_Q^{e(Q/p)}`, `Q` the prime of `S` under `q`. -/
def fibreLocalizationEquivQuotientPow (p : HeightOnePrime R)
    (q : PrimeSpectrum (p.1.asIdeal.Fiber S)) :
    Localization.AtPrime q.asIdeal ≃+*
      Localization.AtPrime (fibrePrimeHeightOne p q).1.asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime (fibrePrimeHeightOne p q).1.asIdeal) ^
          heightOneRamificationIdx (R := R) (fibrePrimeHeightOne p q) := by
  let Q := fibrePrimeHeightOne p q
  let Sr := Localization.AtPrime Q.1.asIdeal
  letI : IsDiscreteValuationRing Sr :=
    heightOnePrime_localRing_isDiscreteValuationRing Q
  have hunder : Q.1.asIdeal.under R = p.1.asIdeal :=
    (Ideal.LiesOver.over (p := p.1.asIdeal)
      (P := q.asIdeal.comap Algebra.TensorProduct.includeRight)).symm
  have h : ((p.1.asIdeal.map (algebraMap R S)).map (algebraMap S Sr) : Ideal Sr) =
      IsLocalRing.maximalIdeal Sr ^ heightOneRamificationIdx (R := R) Q := by
    rw [heightOneRamificationIdx_eq_dvrExponent (R := R) Q,
      ← heightOneDvrExponent_spec (R := R) Q, hunder, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  exact (Ideal.Fiber.algEquivAux₂ p.1.asIdeal q.asIdeal).toRingEquiv.trans
    (Ideal.quotEquivOfEq h)

/-- The fibre ring of `S` over a height-one prime `p` is the product, over its
primes `q`, of `S_Q / 𝔪_Q^{e(Q/p)}`, with `Q` the prime of `S` under `q`. -/
def fibreEquivPiQuotientPow (p : HeightOnePrime R) :
    p.1.asIdeal.Fiber S ≃+*
      ∀ q : PrimeSpectrum (p.1.asIdeal.Fiber S),
        Localization.AtPrime (fibrePrimeHeightOne p q).1.asIdeal ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime (fibrePrimeHeightOne p q).1.asIdeal) ^
            heightOneRamificationIdx (R := R) (fibrePrimeHeightOne p q) :=
  (RingEquiv.ofBijective (PrimeSpectrum.toPiLocalization (p.1.asIdeal.Fiber S))
      ⟨PrimeSpectrum.toPiLocalization_injective _,
        PrimeSpectrum.toPiLocalization_surjective_of_discreteTopology _⟩).trans
    (RingEquiv.piCongrRight fun q => fibreLocalizationEquivQuotientPow p q)

end Algebra

section Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]

/-- The codimension-one points of `X` over a codimension-one point `E` of `Y`. -/
abbrev SchemeDivisorPointsOver (E : SchemeDivisorPoint Y) : Type u :=
  {D : SchemeDivisorPoint X // f D.1 = E.1}

set_option backward.isDefEq.respectTransparency false in
/-- On a chart `U ∋ E`, the primes of the affine fibre ring are exactly the
codimension-one points of `X` over `E`. -/
def fibrePrimeEquivDivisorsOver (U : Y.affineOpens) (E : SchemeDivisorPoint Y)
    (hE : E.1 ∈ (U : Y.Opens)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    PrimeSpectrum ((affinePrimeOfSchemeDivisorPoint E U hE).1.asIdeal.Fiber
        Γ(X, finitePreimageAffine f U)) ≃ SchemeDivisorPointsOver f E := by
  let V := finitePreimageAffine f U
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let p := affinePrimeOfSchemeDivisorPoint E U hE
  let x : X := Function.surjInv f.surjective E.1
  have hfx : f x = E.1 := Function.surjInv_eq f.surjective E.1
  have hxV : x ∈ (V : X.Opens) := by
    change f x ∈ (U : Y.Opens)
    rwa [hfx]
  letI : Nonempty (U : Y.Opens) := ⟨⟨E.1, hE⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨x, hxV⟩⟩
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  refine Equiv.ofBijective
    (fun q => ⟨schemeDivisorPointOfAffinePrime V (fibrePrimeHeightOne p q), ?_⟩) ⟨?_, ?_⟩
  · have hunder : heightOneUnder (R := R) (fibrePrimeHeightOne p q) = p := by
      apply Subtype.ext
      exact PrimeSpectrum.ext
        (Ideal.LiesOver.over (p := p.1.asIdeal)
          (P := q.asIdeal.comap Algebra.TensorProduct.includeRight)).symm
    have hmap := schemeDivisorPointOfAffinePrime_map f U (fibrePrimeHeightOne p q)
    rw [hunder] at hmap
    exact hmap.trans (congrArg Subtype.val (schemeDivisorPointOfAffinePrime_affinePrime E U hE))
  · intro q₁ q₂ h
    have hQ := schemeDivisorPointOfAffinePrime_injective V (congrArg Subtype.val h)
    apply (PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal).symm.injective
    apply Subtype.ext
    exact congrArg (fun Q : HeightOnePrime S => Q.1.asIdeal) hQ
  · rintro ⟨D, hDE⟩
    have hDV : D.1 ∈ (V : X.Opens) := by
      change f D.1 ∈ (U : Y.Opens)
      rwa [hDE]
    let Q := affinePrimeOfSchemeDivisorPoint D V hDV
    have hQrec : schemeDivisorPointOfAffinePrime V Q = D :=
      schemeDivisorPointOfAffinePrime_affinePrime D V hDV
    have hQunder : heightOneUnder (R := R) Q = p := by
      apply schemeDivisorPointOfAffinePrime_injective U
      rw [schemeDivisorPointOfAffinePrime_affinePrime E U hE]
      apply Subtype.ext
      have hmap := schemeDivisorPointOfAffinePrime_map f U Q
      rw [hQrec] at hmap
      exact hmap.symm.trans hDE
    have hlies : Q.1.asIdeal.LiesOver p.1.asIdeal :=
      ⟨(congrArg (fun z : HeightOnePrime R ↦ z.1.asIdeal) hQunder).symm⟩
    let Qo : p.1.asIdeal.primesOver S := ⟨Q.1.asIdeal, inferInstance, hlies⟩
    refine ⟨PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal Qo, ?_⟩
    apply Subtype.ext
    change schemeDivisorPointOfAffinePrime V _ = D
    convert hQrec using 2
    apply Subtype.ext
    apply PrimeSpectrum.ext
    exact congrArg Subtype.val
      ((PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal).symm_apply_apply Qo)

set_option backward.isDefEq.respectTransparency false in
/-- On a chart, the local factor `S_Q / 𝔪^{e}` at a height-one prime `Q` of the
preimage chart is the stalk quotient `𝒪_{X,D} / 𝔪_D^{e(D)}` at the corresponding
divisor `D`, with `e(D)` the actual stalk ramification index. -/
def chartQuotientPowEquivStalk (U : Y.affineOpens)
    (Q : HeightOnePrime Γ(X, finitePreimageAffine f U)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    Localization.AtPrime Q.1.asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime Q.1.asIdeal) ^
          heightOneRamificationIdx (R := Γ(Y, U)) Q ≃+*
      X.presheaf.stalk (schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) Q).1 ⧸
        IsLocalRing.maximalIdeal
            (X.presheaf.stalk (schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) Q).1) ^
          schemeDivisorRamificationIdx f
            (schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) Q) := by
  let V := finitePreimageAffine f U
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.app U).hom.toAlgebra
  have hx : V.2.fromSpec Q.1 ∈ (V : X.Opens) := (V.2.isoSpec.inv Q.1).2
  letI : Algebra Γ(X, V) (X.presheaf.stalk (V.2.fromSpec Q.1)) :=
    X.presheaf.algebra_section_stalk ⟨_, hx⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk (V.2.fromSpec Q.1)) Q.1.asIdeal :=
    V.2.isLocalization_stalk' Q.1 hx
  let φ := (IsLocalization.algEquiv Q.1.asIdeal.primeCompl (Localization.AtPrime Q.1.asIdeal)
    (X.presheaf.stalk (V.2.fromSpec Q.1))).toRingEquiv
  refine Ideal.quotientEquiv _ _ φ ?_
  rw [schemeDivisorRamificationIdx_eq_heightOneRamificationIdx f U Q, Ideal.map_pow]
  congr 1
  exact (IsLocalRing.map_ringEquiv_maximalIdeal φ).symm

set_option backward.isDefEq.respectTransparency false in
/-- On a chart `U ∋ E`, the scheme-theoretic fibre `f.fiber E` is the spectrum
of the affine fibre ring `κ(p) ⊗_R S` of the finite preimage chart. -/
def schemeFiberIsoSpecChartFiber (U : Y.affineOpens) (E : SchemeDivisorPoint Y)
    (hE : E.1 ∈ (U : Y.Opens)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    f.fiber E.1 ≅ Spec (.of ((affinePrimeOfSchemeDivisorPoint E U hE).1.asIdeal.Fiber
        Γ(X, finitePreimageAffine f U))) := by
  let V := finitePreimageAffine f U
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let p := affinePrimeOfSchemeDivisorPoint E U hE
  let y : (U : Y.Opens).toScheme := ⟨E.1, hE⟩
  letI : Algebra R S := (f.app U).hom.toAlgebra
  have hp : p.1 = U.2.primeIdealOf y := by
    apply PrimeSpectrum.ext
    exact pointClosureIdealSheaf_ideal E.1 U hE
  have emap :
      (Spec.map (f.appLE U V le_rfl)).fiber (U.2.primeIdealOf y) =
        (Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiber p.1 := by
    rw [hp]
    congr 2
    exact f.appLE_eq_app
  exact (schemeFiberRestrictIso f U y).symm ≪≫ finiteRestrictFiberIsoSpec f U y ≪≫
    eqToIso emap ≪≫ Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R S p.1)

/-- On a chart `U ∋ E`, the global sections of the scheme-theoretic fibre are
the affine fibre ring `κ(p) ⊗_R S`. -/
def schemeFiberΓEquivChartFiber (U : Y.affineOpens) (E : SchemeDivisorPoint Y)
    (hE : E.1 ∈ (U : Y.Opens)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    Γ(f.fiber E.1, ⊤) ≃+* (affinePrimeOfSchemeDivisorPoint E U hE).1.asIdeal.Fiber
        Γ(X, finitePreimageAffine f U) :=
  letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
  ((Scheme.Γ.mapIso (schemeFiberIsoSpecChartFiber f U E hE).op).symm ≪≫
    Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- The factor ring `𝒪_{X,D} / 𝔪_D^{e(D/E)}` attached to a divisor `D` over `E`. -/
abbrev schemeDivisorFibreFactor (E : SchemeDivisorPoint Y) (D : SchemeDivisorPointsOver f E) :
    Type u :=
  X.presheaf.stalk D.1.1 ⧸
    IsLocalRing.maximalIdeal (X.presheaf.stalk D.1.1) ^ schemeDivisorRamificationIdx f D.1

set_option backward.isDefEq.respectTransparency false in
/-- **`paper-p.tex` l. 364–371, on a chart.** The global sections of the
scheme-theoretic fibre of `f` over a codimension-one point `E` are the product,
over the codimension-one points `D` of `X` above `E`, of
`𝒪_{X,D} / 𝔪_D^{e(D/E)}`. -/
def schemeFiberΓEquivPiOfChart (U : Y.affineOpens) (E : SchemeDivisorPoint Y)
    (hE : E.1 ∈ (U : Y.Opens)) :
    Γ(f.fiber E.1, ⊤) ≃+*
      ∀ D : SchemeDivisorPointsOver f E, schemeDivisorFibreFactor f E D := by
  let V := finitePreimageAffine f U
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let p := affinePrimeOfSchemeDivisorPoint E U hE
  let x : X := Function.surjInv f.surjective E.1
  have hfx : f x = E.1 := Function.surjInv_eq f.surjective E.1
  have hxV : x ∈ (V : X.Opens) := by
    change f x ∈ (U : Y.Opens)
    rwa [hfx]
  letI : Nonempty (U : Y.Opens) := ⟨⟨E.1, hE⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨x, hxV⟩⟩
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  exact (schemeFiberΓEquivChartFiber f U E hE).trans <|
    (fibreEquivPiQuotientPow (R := R) (S := S) p).trans <|
    (RingEquiv.piCongrRight fun q =>
      chartQuotientPowEquivStalk f U (fibrePrimeHeightOne p q)).trans <|
    RingEquiv.piCongrLeft (schemeDivisorFibreFactor f E) (fibrePrimeEquivDivisorsOver f U E hE)

/-- **`paper-p.tex` l. 364–371 (product decomposition).** For a finite dominant
morphism `f : X → Y` of normal integral schemes with `Y` locally Noetherian and a
codimension-one point `E` of `Y`, the ring of global sections of the
scheme-theoretic fibre `f.fiber E` is isomorphic to
`∏_{D ↦ E} 𝒪_{X,D} / 𝔪_D^{e(D/E)}`, the product over the codimension-one points
`D` of `X` with `f D = E`, where `e = schemeDivisorRamificationIdx f`.
An affine chart around `E` is chosen; the target does not depend on it. -/
def schemeFiberΓEquivPi (E : SchemeDivisorPoint Y) :
    Γ(f.fiber E.1, ⊤) ≃+*
      ∀ D : SchemeDivisorPointsOver f E, schemeDivisorFibreFactor f E D :=
  have h : ∃ U : Y.affineOpens, E.1 ∈ (U : Y.Opens) := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hEW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ E.1) isOpen_univ
    exact ⟨⟨W, hW⟩, hEW⟩
  schemeFiberΓEquivPiOfChart f h.choose E h.choose_spec

/-- **`paper-p.tex` l. 364–371 (reducedness).** The scheme-theoretic fibre over
a codimension-one point `E` is reduced exactly when every codimension-one point
above `E` has ramification index one. -/
theorem schemeFiber_isReduced_iff_forall_divisorsOver (E : SchemeDivisorPoint Y) :
    AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      ∀ D : SchemeDivisorPointsOver f E, schemeDivisorRamificationIdx f D.1 = 1 := by
  rw [schemeDivisorFiber_isReduced_iff_forall_schemeDivisorRamificationIdx_eq_one f E]
  exact ⟨fun h D => h D.1 D.2, fun h D hD => h ⟨D, hD⟩⟩

/-- **`paper-p.tex` l. 364–371 (reducedness of the fibre ring).** The ring
`Γ(f.fiber E)` (the product of `paper-p` l. 364–371) is reduced exactly when
every codimension-one point above `E` has ramification index one. -/
theorem schemeFiberΓ_isReduced_iff_forall_divisorsOver (E : SchemeDivisorPoint Y) :
    _root_.IsReduced Γ(f.fiber E.1, ⊤) ↔
      ∀ D : SchemeDivisorPointsOver f E, schemeDivisorRamificationIdx f D.1 = 1 := by
  rw [← schemeFiber_isReduced_iff_forall_divisorsOver]
  obtain ⟨_, ⟨W, hW, rfl⟩, hEW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ E.1) isOpen_univ
  let U : Y.affineOpens := ⟨W, hW⟩
  letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
  let e := schemeFiberIsoSpecChartFiber f U E hEW
  let φ := schemeFiberΓEquivChartFiber f U E hEW
  have h1 : AlgebraicGeometry.IsReduced (f.fiber E.1) ↔
      AlgebraicGeometry.IsReduced (Spec (.of
        ((affinePrimeOfSchemeDivisorPoint E U hEW).1.asIdeal.Fiber
          Γ(X, finitePreimageAffine f U)))) :=
    ⟨fun h => @isReduced_of_isOpenImmersion _ _ e.inv inferInstance h,
      fun h => @isReduced_of_isOpenImmersion _ _ e.hom inferInstance h⟩
  rw [h1, affine_isReduced_iff]
  exact ⟨fun h => isReduced_of_injective φ.symm φ.symm.injective,
    fun h => isReduced_of_injective φ φ.injective⟩

omit [IsNormalScheme X] in
/-- There are finitely many codimension-one points over a codimension-one point. -/
theorem finite_schemeDivisorPointsOver (E : SchemeDivisorPoint Y) :
    Finite (SchemeDivisorPointsOver f E) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hEW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ E.1) isOpen_univ
  let U : Y.affineOpens := ⟨W, hW⟩
  letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
    moduleFinite_finitePreimageAffine f U
  exact Finite.of_equiv _ (fibrePrimeEquivDivisorsOver f U E hEW)

#print axioms finite_schemeDivisorPointsOver
#print axioms fibreEquivPiQuotientPow
#print axioms fibrePrimeEquivDivisorsOver
#print axioms chartQuotientPowEquivStalk
#print axioms schemeFiberIsoSpecChartFiber
#print axioms schemeFiberΓEquivPiOfChart
#print axioms schemeFiberΓEquivPi
#print axioms schemeFiber_isReduced_iff_forall_divisorsOver
#print axioms schemeFiberΓ_isReduced_iff_forall_divisorsOver

end Scheme

end

end Pcf
