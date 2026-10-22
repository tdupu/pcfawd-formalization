/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDeltaNonEtaleCriterion
public import Mathlib.RingTheory.Smooth.Fiber

/-!
# The local converse from ramification index one to formal étaleness

The algebraic converse is proved first for a local flat finitely presented
extension with separable residue fields over the maximal ideal.  The remaining
geometric step is to derive the latter hypothesis at every prime over a divisor
from separability of the actual divisor residue-field extension.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry

universe u v

set_option linter.style.haveILetI false

/-- A local flat finitely presented extension with ramification index one
and separable residue fields over the closed point is formally étale. -/
theorem formallyEtale_of_ramificationIdx_eq_one_of_residueSeparableAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Algebra.HasSeparableResidueFieldsAt R S
      ((IsLocalRing.maximalIdeal S).under R)]
    (hidx : (IsLocalRing.maximalIdeal S).ramificationIdx R = 1) :
    Algebra.FormallyEtale R S := by
  let q := IsLocalRing.maximalIdeal S
  letI : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
  have hunr : Algebra.IsUnramifiedAt R q :=
    (Ideal.ramificationIdx_eq_one_iff).mp hidx
  let e : S ≃ₐ[R] Localization.AtPrime q :=
    (IsLocalization.atUnits S q.primeCompl (by
      intro x hx
      exact (IsLocalRing.notMem_maximalIdeal).mp hx)).restrictScalars R
  haveI : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact (Algebra.Etale.of_formallyUnramified_of_flat).formallyEtale

/-- The same local converse requires separability only at the actual
maximal prime, rather than at every prime over the closed point. -/
theorem formallyEtale_of_ramificationIdx_eq_one_of_residueSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hidx : (IsLocalRing.maximalIdeal S).ramificationIdx R = 1)
    (hsep : let q := IsLocalRing.maximalIdeal S
      letI : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
      let p := IsLocalRing.maximalIdeal R
      letI := Localization.AtPrime.algebraOfLiesOver p q
      Algebra.IsSeparable p.ResidueField q.ResidueField) :
    Algebra.FormallyEtale R S := by
  let q := IsLocalRing.maximalIdeal S
  letI : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
  let p := IsLocalRing.maximalIdeal R
  letI : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  letI : q.LiesOver p := ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hmap : p.map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.ramificationIdx_eq p q, ENat.toNat_eq_iff_eq_natCast,
      Nat.cast_one, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at hidx
    exact hidx
  have hunr : Algebra.IsUnramifiedAt R q :=
    (Algebra.isUnramifiedAt_iff_map_eq R p q).mpr ⟨hsep, hmap⟩
  let e : S ≃ₐ[R] Localization.AtPrime q :=
    (IsLocalization.atUnits S q.primeCompl (by
      intro x hx
      exact (IsLocalRing.notMem_maximalIdeal).mp hx)).restrictScalars R
  haveI : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact (Algebra.Etale.of_formallyUnramified_of_flat).formallyEtale

/-- For a local homomorphism, separability of the ordinary residue-field
extension supplies the prime-residue hypothesis in the local criterion. -/
theorem formallyEtale_of_ramificationIdx_eq_one_of_localResidueSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hidx : (IsLocalRing.maximalIdeal S).ramificationIdx R = 1)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) :
    Algebra.FormallyEtale R S := by
  let q := IsLocalRing.maximalIdeal S
  letI : q.IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
  let p := IsLocalRing.maximalIdeal R
  letI : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  letI : q.LiesOver p := ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hsep' : Algebra.IsSeparable p.ResidueField q.ResidueField :=
    Algebra.isSeparable_residueField_iff.mpr hsep
  exact formallyEtale_of_ramificationIdx_eq_one_of_residueSeparable
    hidx hsep'

/-- The weighted degree-one criterion gives formal étaleness at an actual
divisor stalk whenever that essentially finite-type stalk map has finite
presentation. The proof uses normality for the DVR and flatness hypotheses. -/
theorem schemeDivisorDelta_eq_one_implies_formallyEtale_of_stalkFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X)
    (hfp : letI := (f.stalkMap d.1).hom.toAlgebra
      Algebra.FinitePresentation (Y.presheaf.stalk (f d.1))
        (X.presheaf.stalk d.1))
    (hδ : schemeDivisorDelta f d = 1) :
    (f.stalkMap d.1).hom.FormallyEtale := by
  let R := Y.presheaf.stalk (f d.1)
  let S := X.presheaf.stalk d.1
  letI : Algebra R S := (f.stalkMap d.1).hom.toAlgebra
  letI : IsLocalHom (algebraMap R S) :=
    show IsLocalHom (f.stalkMap d.1).hom from inferInstance
  letI : Algebra.EssFiniteType R S := LocallyOfFiniteType.stalkMap f d.1
  letI : Algebra.FinitePresentation R S := hfp
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
  exact formallyEtale_of_ramificationIdx_eq_one_of_localResidueSeparable
    ((schemeDivisorDelta_eq_one_iff f d).mp hδ).1 hsep

#print axioms formallyEtale_of_ramificationIdx_eq_one_of_residueSeparableAt
#print axioms formallyEtale_of_ramificationIdx_eq_one_of_residueSeparable
#print axioms formallyEtale_of_ramificationIdx_eq_one_of_localResidueSeparable
#print axioms schemeDivisorDelta_eq_one_implies_formallyEtale_of_stalkFinitePresentation

end Pcf
