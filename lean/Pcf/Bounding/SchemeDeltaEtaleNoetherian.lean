/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDeltaEtaleConverse

/-!
# Étaleness from the local weighted degree over a Noetherian DVR

An actual stalk map of a finite scheme morphism is essentially of finite type.
This file removes the unnecessary finite-presentation hypothesis from the
degree-one local criterion when the base stalk is Noetherian.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry
open TensorProduct

universe u v

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- Ramification index one and separable residue fields imply formal
unramifiedness for a local essentially finite-type map. -/
theorem formallyUnramified_of_ramificationIdx_eq_one_of_localResidueSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    (hidx : (IsLocalRing.maximalIdeal S).ramificationIdx R = 1)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) :
    Algebra.FormallyUnramified R S := by
  let q := IsLocalRing.maximalIdeal S
  letI : q.IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
  let p := IsLocalRing.maximalIdeal R
  letI : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  letI : q.LiesOver p := ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hsep' : Algebra.IsSeparable p.ResidueField q.ResidueField :=
    Algebra.isSeparable_residueField_iff.mpr hsep
  have hmap : p.map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.ramificationIdx_eq p q, ENat.toNat_eq_iff_eq_natCast,
      Nat.cast_one, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at hidx
    exact hidx
  have hunr : Algebra.IsUnramifiedAt R q :=
    (Algebra.isUnramifiedAt_iff_map_eq R p q).mpr ⟨hsep', hmap⟩
  let e : S ≃ₐ[R] Localization.AtPrime q :=
    (IsLocalization.atUnits S q.primeCompl (by
      intro x hx
      exact (IsLocalRing.notMem_maximalIdeal).mp hx)).restrictScalars R
  exact Algebra.FormallyUnramified.of_equiv e.symm

/-- The local degree-one criterion needs only essential finite type over a
Noetherian base. The closed fiber is the separable residue field, and the
formal-smooth-fiber criterion then supplies the lifting property. -/
theorem formallyEtale_of_ramificationIdx_eq_one_of_localResidueSeparable_noetherian
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Module.Flat R S]
    (hidx : (IsLocalRing.maximalIdeal S).ramificationIdx R = 1)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) :
    Algebra.FormallyEtale R S := by
  letI : Algebra.FormallyUnramified R S :=
    formallyUnramified_of_ramificationIdx_eq_one_of_localResidueSeparable hidx hsep
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S :=
    (Algebra.FormallyUnramified.iff_map_maximalIdeal_eq.mp
      (inferInstance : Algebra.FormallyUnramified R S)).2
  let e : IsLocalRing.ResidueField S ≃ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R ⊗[R] S := by
    let p := IsLocalRing.maximalIdeal R
    let q := IsLocalRing.maximalIdeal S
    have e₀ : (S ⧸ p.map (algebraMap R S)) ≃ₐ[R ⧸ p]
        (R ⧸ p) ⊗[R] S :=
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p
    have e₁ : (S ⧸ q) ≃ₐ[R ⧸ p] (S ⧸ p.map (algebraMap R S)) :=
      (Ideal.quotientEquivAlgOfEq R hmap.symm).extendScalarsOfSurjective
        IsLocalRing.residue_surjective
    change (S ⧸ q) ≃ₐ[R ⧸ p] (R ⧸ p) ⊗[R] S
    exact e₁.trans e₀
  letI : Algebra.FormallyEtale (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  letI : Algebra.FormallySmooth (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S) :=
    Algebra.FormallySmooth.of_equiv e
  let P := Algebra.EssFiniteType.subalgebra R S
  letI : Algebra.FinitePresentation R P :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  letI : Algebra.FormallySmooth R S :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (Algebra.EssFiniteType.submonoid R S)
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨inferInstance, inferInstance⟩

/-- For a finite dominant map to a normal locally Noetherian integral
scheme, the paper's weighted degree is one exactly when the actual stalk
map at a source divisor is formally étale. -/
theorem schemeDivisorDelta_eq_one_iff_formallyEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X) :
    schemeDivisorDelta f d = 1 ↔
      (f.stalkMap d.1).hom.FormallyEtale := by
  constructor
  · intro hδ
    let R := Y.presheaf.stalk (f d.1)
    let S := X.presheaf.stalk d.1
    letI : Algebra R S := (f.stalkMap d.1).hom.toAlgebra
    letI : IsLocalHom (algebraMap R S) :=
      show IsLocalHom (f.stalkMap d.1).hom from inferInstance
    letI : Algebra.EssFiniteType R S := LocallyOfFiniteType.stalkMap f d.1
    letI : IsDiscreteValuationRing R :=
      (d.mapFiniteDominantNormal f).stalk_isDiscreteValuationRing
    letI : FaithfulSMul R S :=
      (faithfulSMul_iff_algebraMap_injective R S).mpr
        (stalkMap_injective_of_dominant_integral f d.1)
    letI : Module.Flat R S := inferInstance
    have hsepScheme := ((schemeDivisorDelta_eq_one_iff f d).mp hδ).2
    let Acan : Algebra (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) := inferInstance
    have hA : Acan = (f.residueFieldMap d.1).hom.toAlgebra := by
      apply Algebra.algebra_ext
      intro a
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
      exact IsLocalRing.ResidueField.algebraMap_residue r
    have hsep : Algebra.IsSeparable (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) := by
      rw [← hA] at hsepScheme
      exact hsepScheme
    exact formallyEtale_of_ramificationIdx_eq_one_of_localResidueSeparable_noetherian
      ((schemeDivisorDelta_eq_one_iff f d).mp hδ).1 hsep
  · exact schemeDivisorDelta_eq_one_of_formallyEtale f d

/-- The weighted critical divisor locus equals the non-formally-étale
divisor locus for a finite dominant map to a normal locally Noetherian
integral scheme. -/
theorem schemeDivisorWeightedCritical_eq_nonEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] :
    {d : SchemeDivisorPoint X | 1 < schemeDivisorDelta f d} =
      schemeDivisorNonEtaleLocus f := by
  ext d
  have hpos : 0 < schemeDivisorDelta f d :=
    schemeDivisorDelta_pos_of_isFinite f d
  simp only [Set.mem_ofPred_eq, schemeDivisorNonEtaleLocus]
  constructor
  · intro hδ hét
    have hδ1 := (schemeDivisorDelta_eq_one_iff_formallyEtale f d).2 hét
    omega
  · intro hét
    by_contra hδ
    have hδ1 : schemeDivisorDelta f d = 1 := by omega
    exact hét ((schemeDivisorDelta_eq_one_iff_formallyEtale f d).1 hδ1)

#print axioms formallyUnramified_of_ramificationIdx_eq_one_of_localResidueSeparable
#print axioms formallyEtale_of_ramificationIdx_eq_one_of_localResidueSeparable_noetherian
#print axioms schemeDivisorDelta_eq_one_iff_formallyEtale
#print axioms schemeDivisorWeightedCritical_eq_nonEtale

end Pcf
