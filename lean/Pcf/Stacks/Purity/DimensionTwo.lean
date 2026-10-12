/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.SchemeBridge
import Pcf.Stacks.Purity.DiscriminantGlobal
import Pcf.Stacks.Purity.HeightOneEtaleBridge
import Pcf.Stacks.Purity.MiracleFlatnessTwo
import Pcf.Stacks.Purity.Tag0BMBAssembly

/-!
# The dimension-two case of Stacks Tag `0BMA`

This file proves the affine purity statement used in Stacks Tag `0BMA` for a two-dimensional
regular local ring.  The input is the literal target predicate from Tag `0BM9`: the algebra is
finite, torsion-free, Stacks-normal, and its affine spectrum is etale after pullback to the
punctured spectrum.

There is no locality or connectedness hypothesis on the finite algebra.  Miracle flatness first
makes it finite free.  The scheme-theoretic punctured-etale hypothesis is then converted into
pointwise etaleness at every nonclosed source prime.  In codimension one this makes the localized
discriminant a unit.  The principal ideal theorem makes the discriminant a unit on the base, and
the disconnected discriminant criterion finishes the proof.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option linter.style.haveILetI false

universe u v

namespace Pcf.Stacks

set_option backward.isDefEq.respectTransparency false in
/-- The literal scheme pullback condition in the Tag `0BM9` target implies algebraic etaleness at
every source prime lying over the punctured spectrum.

The proof identifies the pullback with the restriction of `Spec S → Spec R` over the puncture,
uses etaleness on the restricted stalk, and transports that stalk statement through the standard
affine-spectrum localization isomorphism. -/
theorem Algebra.isEtaleAt_of_puncturedSpectrum_pullback_etale
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R]
    (hpullback : Etale (((Over.pullback (puncturedSpectrum R).ι).obj
      ((algSpec (.of R)).obj (Opposite.op (.of R S)))).hom))
    (q : Ideal S) [q.IsPrime]
    (hq : q.under R ≠ IsLocalRing.maximalIdeal R) :
    Algebra.IsEtaleAt R q := by
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let U : (Spec (.of R)).Opens := puncturedSpectrum R
  change Etale (pullback.snd f U.ι) at hpullback
  let e : Arrow.mk (pullback.snd f U.ι) ≅ Arrow.mk (f ∣_ U) :=
    Arrow.isoMk (pullbackRestrictIsoRestrict f U) (Iso.refl _) (by simp)
  letI : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale) := by
    rw [AlgebraicGeometry.HasRingHomProperty.eq_affineLocally
      (@AlgebraicGeometry.Etale)]
    exact AlgebraicGeometry.affineLocally_respectsIso _ RingHom.Etale.respectsIso
  have hfU : Etale (f ∣_ U) :=
    (MorphismProperty.arrow_mk_iso_iff (@AlgebraicGeometry.Etale) e).mp hpullback
  let x : Spec (.of S) := ⟨q, inferInstance⟩
  have hfx : f x ∈ U := by
    change f x ∈ puncturedSpectrum R
    rw [mem_puncturedSpectrum_iff R (f x)]
    intro hx
    apply hq
    change Ideal.comap (algebraMap R S) q = IsLocalRing.maximalIdeal R
    simpa only [f, x, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
      CommRingCat.hom_ofHom, IsLocalRing.closedPoint] using
        congrArg PrimeSpectrum.asIdeal hx
  let xU : f ⁻¹ᵁ U := ⟨x, hfx⟩
  have hrestricted : ((f ∣_ U).stalkMap xU).hom.FormallyEtale :=
    AlgebraicGeometry.Etale.stalkMap_formallyEtale hfU xU
  have hstalk : (f.stalkMap x).hom.FormallyEtale :=
    (formallyEtale_respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U xU)).mp hrestricted
  have hlocalRing :
      (Localization.localRingHom (q.under R) q (algebraMap R S) rfl).FormallyEtale := by
    have hlocalRing' := (formallyEtale_respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso
        (CommRingCat.ofHom (algebraMap R S)) x)).mp hstalk
    change (Localization.localRingHom
      (Ideal.comap (algebraMap R S) q) q (algebraMap R S) rfl).FormallyEtale at hlocalRing'
    change (Localization.localRingHom
      (Ideal.comap (algebraMap R S) q) q (algebraMap R S) rfl).FormallyEtale
    exact hlocalRing'
  let p : Ideal R := q.under R
  letI : p.IsPrime := Ideal.IsPrime.under R q
  letI : q.LiesOver p := ⟨rfl⟩
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    inferInstance
  have hlocal : Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime q) := by
    rw [← RingHom.formallyEtale_algebraMap,
      Localization.AtPrime.algebraMap_eq p q]
    exact hlocalRing
  letI : Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime q) := hlocal
  exact Algebra.FormallyEtale.comp R (Localization.AtPrime p) (Localization.AtPrime q)

/-- A two-dimensional regular local ring has a height-one prime.  This small consequence of a
regular system of parameters is used only to rule out a zero discriminant from the height-one
unit tests. -/
theorem exists_prime_height_one_of_isRegularLocalRing_dimension_two
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) :
    ∃ p : Ideal R, p.IsPrime ∧ p.height = 1 := by
  letI : IsDomain R := isDomain_of_isRegularLocalRing R
  obtain ⟨x, y, hspan, hx, _⟩ :=
    exists_regular_pair_span_maximalIdeal_of_dimension_two hdim
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    exact IsSMulRegular.not_zero hx
  have hxu : ¬ IsUnit x := by
    intro hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal R := by
      rw [← hspan]
      exact Ideal.subset_span (Set.mem_insert x {y})
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
    exact hxm hxu
  obtain ⟨p, hp⟩ := (Ideal.span {x}).nonempty_minimalPrimes (by simpa using hxu)
  letI : p.IsPrime := hp.isPrime
  have hxp : x ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton x))
  have hp_ne_bot : p ≠ ⊥ := by
    intro hp0
    rw [hp0, Ideal.mem_bot] at hxp
    exact hx0 hxp
  refine ⟨p, inferInstance, le_antisymm ?_ ?_⟩
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {x}) p hp
  · rw [Order.one_le_iff_ne_zero]
    intro hp0
    exact hp_ne_bot (Ideal.height_eq_zero_iff_eq_bot.mp hp0)

/-- The dimension-two finite-normal endpoint after supplying normality of the regular base.

For a two-dimensional regular local ring, every finite torsion-free Stacks-normal algebra whose
spectrum is etale over the punctured spectrum is etale.  The finite algebra may be disconnected
and is not assumed local; generic and codimension-one etaleness are derived from the literal
scheme pullback hypothesis.

The explicit `IsIntegrallyClosed R` argument records the one result about regular local rings
which is not yet available at the pinned Mathlib revision. -/
theorem finiteNormalPuncturedEtalePurity_of_isRegularLocalRing_of_isIntegrallyClosed_dimension_two
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] [IsIntegrallyClosed R] (hdim : ringKrullDim R = 2) :
    FiniteNormalPuncturedEtalePurity R := by
  intro B hB
  let S : Type u := B.unop
  letI : CommRing S := inferInstance
  letI : Algebra R S := inferInstance
  letI : Module.Finite R S := hB.1
  letI : Module.IsTorsionFree R S := hB.2.1
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have hnormal : IsStacksNormalRing S := hB.2.2.1
  letI : IsDomain R := isDomain_of_isRegularLocalRing R
  letI : Module.Free R S :=
    Module.free_of_finite_torsionFree_stacksNormal_dimension_two hnormal hdim
  letI : Module.FinitePresentation R S :=
    Module.finitePresentation_of_finite R S
  letI : Algebra.FinitePresentation R S := inferInstance
  letI : Module.Flat R S := inferInstance
  let ι := Module.Free.ChooseBasisIndex R S
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  have hunramified : ∀ (q : Ideal S) [q.IsPrime], q.height = 1 →
      Algebra.IsUnramifiedAt R q := by
    intro q hqprime hqheight
    have hpheight : (q.under R).height = 1 := by
      rw [Ideal.height_under_eq_of_finite_of_flat (R := R) q]
      exact hqheight
    have hpne : q.under R ≠ IsLocalRing.maximalIdeal R := by
      intro hp
      rw [hp] at hpheight
      have hmax : (IsLocalRing.maximalIdeal R).height = 2 := by
        exact WithBot.coe_eq_coe.mp
          (IsLocalRing.maximalIdeal_height_eq_ringKrullDim.trans hdim)
      rw [hmax] at hpheight
      norm_num at hpheight
    letI : Algebra.IsEtaleAt R q :=
      Algebra.isEtaleAt_of_puncturedSpectrum_pullback_etale hB.2.2.2 q hpne
    exact inferInstance
  have hheightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Algebra.Etale (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[R] S) := by
    intro p hpprime hpheight
    exact Algebra.etale_heightOne_baseChange_of_unramifiedAt_height_one
      hunramified p hpheight
  have hunitHeightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap R (Localization.AtPrime p) (Algebra.discr R b)) := by
    intro p hpprime hpheight
    letI : Algebra.Etale (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[R] S) := hheightOne p hpheight
    exact Algebra.isUnit_map_discr_of_etale_baseChange b p
  have hdisc0 : Algebra.discr R b ≠ 0 := by
    obtain ⟨p, hpprime, hpheight⟩ :=
      exists_prime_height_one_of_isRegularLocalRing_dimension_two R hdim
    letI : p.IsPrime := hpprime
    have hu := hunitHeightOne p hpheight
    exact fun hzero ↦ hu.ne_zero (by simp [hzero])
  have hdisc : IsUnit (Algebra.discr R b) :=
    isUnit_of_isUnit_localizationAt_height_one hdisc0 hunitHeightOne
  exact Algebra.etale_of_isUnit_discr_of_basis_global b hdisc

end Pcf.Stacks

#print axioms Pcf.Stacks.Algebra.isEtaleAt_of_puncturedSpectrum_pullback_etale
#print axioms Pcf.Stacks.exists_prime_height_one_of_isRegularLocalRing_dimension_two
#print axioms
  Pcf.Stacks.finiteNormalPuncturedEtalePurity_of_isRegularLocalRing_of_isIntegrallyClosed_dimension_two
