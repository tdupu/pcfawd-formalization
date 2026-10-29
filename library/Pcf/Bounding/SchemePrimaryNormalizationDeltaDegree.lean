/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryNormalizationResidueDegree
public import Pcf.Bounding.SchemeDeltaDynamics

/-!
# The scheme divisor weight of a finite primary normalization

At a codimension-one point of the actual finite normalization in a
purely inseparable function-field extension, the weighted local degree
is the degree of that field extension. This is the local numerical
identity used in `paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

theorem schemeFieldExtensionNormalization_divisorDelta_eq_genericDegree
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [IsPurelyInseparable X.functionField L]
    [IsFinite (schemeFieldExtensionInclusion X L).fromNormalization]
    [IsDominant (schemeFieldExtensionInclusion X L).fromNormalization]
    [IsIntegral (schemeFieldExtensionInclusion X L).normalization]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    (d : SchemeDivisorPoint (schemeFieldExtensionInclusion X L).normalization)
    (hd : d.1 ∈ (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ
      (U : X.Opens))
    (pchar : ℕ) [ExpChar X.functionField pchar]
    [ExpChar ((U.2.primeIdealOf
      ⟨(schemeFieldExtensionInclusion X L).fromNormalization d.1, hd⟩).asIdeal).ResidueField
      pchar] :
    schemeDivisorDelta (schemeFieldExtensionInclusion X L).fromNormalization d =
      Module.finrank X.functionField L := by
  let f := schemeFieldExtensionInclusion X L
  let g := f.fromNormalization
  let V := finitePreimageAffine g U
  let R := Γ(X, U)
  let K := X.functionField
  let Rp := Localization.AtPrime
    ((U.2.primeIdealOf ⟨g d.1, hd⟩).asIdeal)
  let p := (U.2.primeIdealOf ⟨g d.1, hd⟩).asIdeal
  let q := (V.2.primeIdealOf ⟨d.1, hd⟩).asIdeal
  letI : Algebra R L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap K L)).hom.toAlgebra
  letI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R Γ(f.normalization, V) := (g.app U).hom.toAlgebra
  letI : Algebra R Γ(f.normalization, g ⁻¹ᵁ (U : X.Opens)) :=
    (g.app U).hom.toAlgebra
  letI : IsFractionRing R K :=
    functionField_isFractionRing_of_isAffineOpen X U U.2
  let e := schemeFieldExtensionNormalizationIntegralClosureAlgEquiv X L U U.2
  letI : Algebra R (integralClosure R L) := inferInstance
  haveI : q.IsPrime := (V.2.primeIdealOf ⟨d.1, hd⟩).isPrime
  let q' : Ideal Γ(f.normalization, g ⁻¹ᵁ (U : X.Opens)) := q
  haveI : q'.IsPrime := ‹q.IsPrime›
  let P := q'.map e
  haveI : p.IsPrime := (U.2.primeIdealOf ⟨g d.1, hd⟩).isPrime
  haveI : P.IsPrime := by
    dsimp [P]
    exact Ideal.map_isPrime_of_equiv e
  have hcontractLE : p = q.comap (g.appLE U V le_rfl).hom := by
    simpa only [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) U.2
          (V : f.normalization.Opens) V.2 le_rfl hd)).symm
  have hcontract : p = q.comap (g.app U).hom := by
    have happ : (g.appLE U V le_rfl).hom = (g.app U).hom :=
      congrArg CommRingCat.Hom.hom g.appLE_eq_app
    rw [happ] at hcontractLE
    exact hcontractLE
  letI : q.LiesOver p := ⟨hcontract⟩
  letI : q'.LiesOver p := ‹q.LiesOver p›
  letI : P.LiesOver p := Ideal.map_equiv_liesOver q' p e
  have hpheight : p.height = 1 := by
    let b := d.mapFiniteDominantNormal g
    have h := pointClosureIdealSheaf_ideal_height b U hd
    change ((pointClosureIdealSheaf (g d.1)).ideal U).height = 1 at h
    rw [pointClosureIdealSheaf_ideal (g d.1) U hd] at h
    exact h
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsDiscreteValuationRing Rp :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne p hpheight
  letI : IsDedekindDomain Rp := inferInstance
  letI : Algebra Rp K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Rp K
      p.primeCompl (nonZeroDivisors R) p.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower R Rp K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Rp K
      p.primeCompl (nonZeroDivisors R) p.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing Rp K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rp K
  letI : Algebra Rp L := ((algebraMap K L).comp (algebraMap Rp K)).toAlgebra
  letI : IsScalarTower Rp K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R Rp L := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap K L (algebraMap R K r) =
      algebraMap K L (algebraMap Rp K (algebraMap R Rp r))
    rw [← IsScalarTower.algebraMap_apply R Rp K])
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply R K L] using hab
  haveI : Module.Finite R (integralClosure R L) :=
    schemeFieldExtensionNormalizationIntegralClosure_moduleFinite X L U U.2
  have hp0 : IsLocalRing.maximalIdeal Rp ≠ ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq (R := Rp)).not.mp
      (IsLocalization.AtPrime.not_isField R (p.ne_bot_of_height_eq_one hpheight) Rp)
  letI : ExpChar (IsLocalRing.maximalIdeal Rp).ResidueField pchar :=
    (residueFieldEquivOfLocalizationAtPrime R Rp p).symm.toRingHom.expChar
      (residueFieldEquivOfLocalizationAtPrime R Rp p).symm.injective pchar
  have hram : schemeDivisorRamificationIdx g d = P.ramificationIdx R := by
    have hq' : q' = (affinePrimeOfSchemeDivisorPoint d V hd).1.asIdeal := by
      change (V.2.primeIdealOf ⟨d.1, hd⟩).asIdeal =
        (pointClosureIdealSheaf d.1).ideal V
      exact (pointClosureIdealSheaf_ideal d.1 V hd).symm
    change schemeDivisorRamificationIdx g d = (q'.map e).ramificationIdx R
    rw [hq']
    exact schemeFieldExtensionNormalization_ramificationIdx_eq_integralClosure
      X L U d hd
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI : Algebra (X.residueField (g d.1)) (f.normalization.residueField d.1) :=
    (g.residueFieldMap d.1).hom.toAlgebra
  let algCanon : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (g.appLE U V le_rfl).hom hcontractLE).toAlgebra
  have hdegreeAffine :
      @Field.finInsepDegree p.ResidueField q.ResidueField _ _ algCanon =
        Field.finInsepDegree (X.residueField (g d.1))
          (f.normalization.residueField d.1) := by
    letI : Algebra p.ResidueField q.ResidueField := algCanon
    exact schemeFieldExtensionNormalization_residueInsepDegree_eq_affine
      X L U d.1 hd pchar
  letI := Localization.AtPrime.algebraOfLiesOver p q'
  have heqAlg :
      (IsLocalRing.ResidueField.instAlgebra : Algebra p.ResidueField q'.ResidueField) =
        algCanon := by
    apply Algebra.algebra_ext
    intro r
    have hmap : (algebraMap p.ResidueField q'.ResidueField) =
        Ideal.ResidueField.map p q' (g.appLE U V le_rfl).hom hcontractLE := by
      apply IsFractionRing.ringHom_ext (A := R ⧸ p)
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [Ideal.algebraMap_quotient_residueField_mk]
      rw [← IsScalarTower.algebraMap_apply R p.ResidueField q'.ResidueField]
      rw [Ideal.ResidueField.map_algebraMap p q'
        (g.appLE U V le_rfl).hom hcontractLE s]
      have happ : (g.appLE U V le_rfl).hom = (g.app U).hom :=
        congrArg CommRingCat.Hom.hom g.appLE_eq_app
      rw [happ]
      exact (IsScalarTower.algebraMap_apply R
        Γ(f.normalization, g ⁻¹ᵁ (U : X.Opens)) q'.ResidueField s).symm
    exact congrArg (fun h : p.ResidueField →+* q'.ResidueField => h r) hmap
  have hdegreeMap : Field.finInsepDegree p.ResidueField P.ResidueField =
      @Field.finInsepDegree p.ResidueField q.ResidueField _ _ algCanon := by
    have h := finInsepDegree_residueField_map_algEquiv e p q'
    have h' : Field.finInsepDegree p.ResidueField P.ResidueField =
        @Field.finInsepDegree p.ResidueField q'.ResidueField _ _
          IsLocalRing.ResidueField.instAlgebra := h
    exact h'.trans (congrArg
      (fun a : Algebra p.ResidueField q'.ResidueField =>
        @Field.finInsepDegree p.ResidueField q'.ResidueField _ _ a) heqAlg)
  have hpureP : IsPurelyInseparable p.ResidueField P.ResidueField :=
    Bounding.PrimaryFibres.integralClosure_residueField_isPurelyInseparable_at_prime
      R K L p P pchar
  have hglobal : P.ramificationIdx R *
      Field.finInsepDegree p.ResidueField P.ResidueField = Module.finrank K L :=
    integralClosure_delta_eq_genericDegree_atPrime R Rp K L p hinj pchar hp0 P hpureP
  unfold schemeDivisorDelta
  rw [hram, ← hdegreeAffine, ← hdegreeMap]
  exact hglobal

#print axioms schemeFieldExtensionNormalization_divisorDelta_eq_genericDegree

end
end Pcf
