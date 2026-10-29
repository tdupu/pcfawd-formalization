/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryNormalizationChart
public import Pcf.Bounding.AffineSchemeRamification

/-!
# Codimension-one localization in a field-extension normalization

The integral-closure chart of `paper-p.tex`, Lemma `lem:pcf-transfer-charp`,
has actual scheme stalks given by localization at transported prime ideals.
This is the input needed to compare ramification and residue-field degrees
with the local integral-closure calculation.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

variable (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]

/-- The ramification index of an ideal is preserved by an algebra
equivalence over the base ring. -/
theorem ramificationIdx_map_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (q : Ideal S) [q.IsPrime] :
    (q.map e).ramificationIdx R = q.ramificationIdx R := by
  let p := q.under R
  let Sq := Localization.AtPrime q
  let q' := q.map e
  haveI : q'.IsPrime := inferInstance
  let Sq' := Localization.AtPrime q'
  let hmap : q = q'.comap e := by
    exact (Ideal.comap_map_of_bijective e e.bijective).symm
  let f : Sq ≃ₐ[R] Sq' :=
    Localization.localAlgEquiv q q' e hmap
  let : Algebra Sq Sq' := f.toRingHom.toAlgebra
  have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f.toAlgHom
  let z : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq]
      Sq' ⧸ p.map (algebraMap R Sq') :=
    Ideal.quotientEquivAlg _ _
      (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
      (by
        rw [IsScalarTower.algebraMap_eq R Sq Sq', Ideal.map_map]
        congr 1)
  rw [Ideal.ramificationIdx_eq p q,
    Ideal.ramificationIdx_eq p q',
    z.toLinearEquiv.length_eq, Module.length_eq_of_surjective f.surjective]

/-- An algebra equivalence of affine covers preserves the inseparable
degree of the residue extension over a fixed base prime. -/
theorem finInsepDegree_residueField_map_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    letI := Localization.AtPrime.algebraOfLiesOver p (q.map e)
    Field.finInsepDegree p.ResidueField (q.map e).ResidueField =
      Field.finInsepDegree p.ResidueField q.ResidueField := by
  let q' := q.map e
  haveI : q'.IsPrime := inferInstance
  haveI : q'.LiesOver p := Ideal.map_equiv_liesOver q p e
  letI := Localization.AtPrime.algebraOfLiesOver p q
  letI := Localization.AtPrime.algebraOfLiesOver p q'
  have hmap : q = q'.comap e :=
    (Ideal.comap_map_of_bijective e e.bijective).symm
  exact (Field.finInsepDegree_eq_of_equiv p.ResidueField q.ResidueField
    q'.ResidueField (Ideal.residueFieldAlgEquiv' p q q' e hmap)).symm

/-- The affine normalization chart isomorphism commutes with the map from
the original affine chart. This is the algebra compatibility required for
ramification indices. -/
def schemeFieldExtensionNormalizationIntegralClosureAlgEquiv
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let f := schemeFieldExtensionInclusion X L
    letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
      (f.fromNormalization.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) L := by
  let f := schemeFieldExtensionInclusion X L
  letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  letI : Algebra Γ(X, U) Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    (f.fromNormalization.app U).hom.toAlgebra
  let e₀ := f.normalizationObjIso hU
  have he₀ : f.fromNormalization.app U ≫ e₀.hom =
      CommRingCat.ofHom (algebraMap Γ(X, U)
        (integralClosure Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U))) := by
    rw [f.fromNormalization_app hU]
    simp
  let ea₀ : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) :=
    { e₀.commRingCatIsoToRingEquiv with
      commutes' r := congr($(he₀) r) }
  exact ea₀.trans (schemeFieldExtensionSectionsAlgEquiv X L U).mapIntegralClosure

/-- Finiteness of the actual normalization map gives module finiteness of
the corresponding integral-closure chart. -/
theorem schemeFieldExtensionNormalizationIntegralClosure_moduleFinite
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsFinite (schemeFieldExtensionInclusion X L).fromNormalization] :
    let f := schemeFieldExtensionInclusion X L
    letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) := by
  let f := schemeFieldExtensionInclusion X L
  letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  letI : Algebra Γ(X, U) Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    (f.fromNormalization.app U).hom.toAlgebra
  haveI : Module.Finite Γ(X, U)
      Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    RingHom.finite_algebraMap.mp (f.fromNormalization.finite_app U hU)
  exact Module.Finite.equiv
    (schemeFieldExtensionNormalizationIntegralClosureAlgEquiv X L U hU).toLinearEquiv

/-- The ramification index of the actual finite normalization morphism at
a divisor equals the ramification index of the corresponding prime in
the integral closure of an affine base chart. -/
theorem schemeFieldExtensionNormalization_ramificationIdx_eq_integralClosure
    [IsFinite (schemeFieldExtensionInclusion X L).fromNormalization]
    [IsDominant (schemeFieldExtensionInclusion X L).fromNormalization]
    [IsIntegral (schemeFieldExtensionInclusion X L).normalization]
    [IsLocallyNoetherian X] [IsNormalScheme X]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    (d : SchemeDivisorPoint (schemeFieldExtensionInclusion X L).normalization)
    (hd : d.1 ∈ (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ
      (U : X.Opens)) :
    let f := schemeFieldExtensionInclusion X L
    let V := finitePreimageAffine f.fromNormalization U
    letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ (U : X.Opens)) :=
      (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    let e := schemeFieldExtensionNormalizationIntegralClosureAlgEquiv X L U U.2
    let q := (affinePrimeOfSchemeDivisorPoint d V hd).1.asIdeal
    letI : Algebra Γ(X, U) (integralClosure Γ(X, U) L) := inferInstance
    schemeDivisorRamificationIdx f.fromNormalization d = (q.map e).ramificationIdx Γ(X, U) := by
  let f := schemeFieldExtensionInclusion X L
  let V := finitePreimageAffine f.fromNormalization U
  letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ (U : X.Opens)) :=
    (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  letI : Algebra Γ(X, U) Γ(f.normalization, V) :=
    (f.fromNormalization.app U).hom.toAlgebra
  letI : Algebra Γ(X, U)
      Γ((schemeFieldExtensionInclusion X L).normalization,
        (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ (U : X.Opens)) :=
    ((schemeFieldExtensionInclusion X L).fromNormalization.app U).hom.toAlgebra
  let e := schemeFieldExtensionNormalizationIntegralClosureAlgEquiv X L U U.2
  let q := (affinePrimeOfSchemeDivisorPoint d V hd).1.asIdeal
  haveI : q.IsPrime := (affinePrimeOfSchemeDivisorPoint d V hd).1.isPrime
  letI : Algebra Γ(X, U) (integralClosure Γ(X, U) L) := inferInstance
  letI : Module.Finite Γ(X, U) Γ(f.normalization, V) :=
    moduleFinite_finitePreimageAffine f.fromNormalization U
  have hrec : schemeDivisorPointOfAffinePrime V
      (affinePrimeOfSchemeDivisorPoint d V hd) = d :=
    schemeDivisorPointOfAffinePrime_affinePrime d V hd
  change schemeDivisorRamificationIdx f.fromNormalization d =
    (q.map e).ramificationIdx Γ(X, U)
  calc
    schemeDivisorRamificationIdx f.fromNormalization d =
        schemeDivisorRamificationIdx f.fromNormalization
          (schemeDivisorPointOfAffinePrime V
            (affinePrimeOfSchemeDivisorPoint d V hd)) := by rw [hrec]
    _ = q.ramificationIdx Γ(X, U) := by
      exact schemeDivisorRamificationIdx_eq_heightOneRamificationIdx
        f.fromNormalization U (affinePrimeOfSchemeDivisorPoint d V hd)
    _ = (q.map e).ramificationIdx Γ(X, U) := by
      exact (@ramificationIdx_map_algEquiv
        (Γ(X, U)) (Γ(f.normalization, V)) (integralClosure Γ(X, U) L)
        _ _ _ (f.fromNormalization.app U).hom.toAlgebra
        (inferInstance : Algebra Γ(X, U) (integralClosure Γ(X, U) L))
        e q ‹q.IsPrime›).symm

/-- Under the normalization chart equivalence, a stalk is localized at
the prime ideal of the integral closure corresponding to its point. -/
theorem schemeFieldExtensionNormalizationStalk_isLocalizationAtPrime
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (y : (schemeFieldExtensionInclusion X L).normalization)
    (hy : y ∈ (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ U) :
    let f := schemeFieldExtensionInclusion X L
    let V := f.fromNormalization ⁻¹ᵁ U
    let hV : IsAffineOpen V := hU.preimage f.fromNormalization
    let yV : V := ⟨y, hy⟩
    letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    let e := schemeFieldExtensionNormalizationIntegralClosureEquiv X L U hU
    let q := (hV.primeIdealOf yV).asIdeal
    let Q := q.comap e.symm.toRingHom
    letI : Algebra (integralClosure Γ(X, U) L)
        (f.normalization.presheaf.stalk (yV : f.normalization)) :=
      ((f.normalization.presheaf.germ V y hy).hom.comp e.symm.toRingHom).toAlgebra
    IsLocalization.AtPrime
      (f.normalization.presheaf.stalk (yV : f.normalization)) Q := by
  let f := schemeFieldExtensionInclusion X L
  let V := f.fromNormalization ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f.fromNormalization
  let yV : V := ⟨y, hy⟩
  letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  let e := schemeFieldExtensionNormalizationIntegralClosureEquiv X L U hU
  let q := (hV.primeIdealOf yV).asIdeal
  let Q := q.comap e.symm.toRingHom
  haveI : Q.IsPrime := inferInstance
  letI : Algebra (integralClosure Γ(X, U) L)
      (f.normalization.presheaf.stalk (yV : f.normalization)) :=
    ((f.normalization.presheaf.germ V y hy).hom.comp e.symm.toRingHom).toAlgebra
  have hloc := schemeFieldExtensionNormalizationStalk_isLocalization X L U hU y hy
  have hsets : Q.primeCompl = q.primeCompl.map e := by
    ext b
    constructor
    · intro hb
      obtain ⟨a, rfl⟩ := e.surjective b
      exact ⟨a, by simpa [Q, Ideal.mem_primeCompl_iff] using hb, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      simpa [Q, Ideal.mem_primeCompl_iff] using ha
  change IsLocalization Q.primeCompl
    (f.normalization.presheaf.stalk (yV : f.normalization))
  rw [hsets]
  exact hloc

/-- The residue field of the scheme point is canonically isomorphic to
the residue field of its prime in the integral-closure affine chart. -/
def schemeFieldExtensionNormalizationResidueFieldEquiv
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (y : (schemeFieldExtensionInclusion X L).normalization)
    (hy : y ∈ (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ U) :
    let f := schemeFieldExtensionInclusion X L
    let V := f.fromNormalization ⁻¹ᵁ U
    let hV : IsAffineOpen V := hU.preimage f.fromNormalization
    let yV : V := ⟨y, hy⟩
    letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    let e := schemeFieldExtensionNormalizationIntegralClosureEquiv X L U hU
    let Q := (hV.primeIdealOf yV).asIdeal.comap e.symm.toRingHom
    Q.ResidueField ≃+* f.normalization.residueField (yV : f.normalization) := by
  let f := schemeFieldExtensionInclusion X L
  let V := f.fromNormalization ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f.fromNormalization
  let yV : V := ⟨y, hy⟩
  letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  let e := schemeFieldExtensionNormalizationIntegralClosureEquiv X L U hU
  let Q := (hV.primeIdealOf yV).asIdeal.comap e.symm.toRingHom
  haveI : Q.IsPrime := inferInstance
  letI : Algebra (integralClosure Γ(X, U) L)
      (f.normalization.presheaf.stalk (yV : f.normalization)) :=
    ((f.normalization.presheaf.germ V y hy).hom.comp e.symm.toRingHom).toAlgebra
  letI : IsLocalization.AtPrime
      (f.normalization.presheaf.stalk (yV : f.normalization)) Q :=
    schemeFieldExtensionNormalizationStalk_isLocalizationAtPrime X L U hU y hy
  exact IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
      (f.normalization.presheaf.stalk (yV : f.normalization))).toRingEquiv

#print axioms schemeFieldExtensionNormalizationStalk_isLocalizationAtPrime
#print axioms schemeFieldExtensionNormalizationResidueFieldEquiv
#print axioms schemeFieldExtensionNormalizationIntegralClosureAlgEquiv
#print axioms ramificationIdx_map_algEquiv
#print axioms finInsepDegree_residueField_map_algEquiv
#print axioms schemeFieldExtensionNormalizationIntegralClosure_moduleFinite
#print axioms schemeFieldExtensionNormalization_ramificationIdx_eq_integralClosure

end
end Pcf
