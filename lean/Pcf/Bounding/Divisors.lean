/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.SpectrumDynamics
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Localization.Saturation
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Codimension-one points under a finite normal map

This file supplies the affine divisor part of the bridge requested in `HANDOFF.md` §9.
For a finite injective map `R → S`, with `R` normal and `S` a domain, contraction
preserves the height of prime ideals.  It therefore gives a surjective map on height-one
primes.  Their local rings are proved to be DVRs, and Mathlib's length-theoretic
ramification index is proved equal to the exponent of the contracted prime in the maximal
ideal of the source DVR.

This removes the dimension-theoretic and ramification-fidelity obstructions recorded in
`AXIOMS.md` §B.7.  It also constructs the honest contraction map from a normalized
height-one prime to a point of a possibly nonnormal target and proves its fibers finite,
both affinely and for scheme morphisms.  For a finite-type domain over a field,
Noether normalization also proves height preservation without normality of the target.
This supplies the affine divisor contraction, its surjectivity and its finite fibers
over a possibly nonnormal target.  The scheme-global construction and the identification
of the abstract `crit₁` predicate with the non-étale locus are separate bridges.
-/

@[expose] public section

open TopologicalSpace
open scoped BigOperators

namespace Pcf

/-- The codimension-one points of a scheme. -/
def SchemeDivisorPoint (X : AlgebraicGeometry.Scheme) :=
  {x : X // Order.coheight x = 1}

/-- The affine incarnation of an integral effective divisor on a Noetherian integral
scheme: a height-one prime. -/
abbrev HeightOnePrime (A : Type*) [CommRing A] :=
  {p : PrimeSpectrum A // p.asIdeal.height = 1}

/-- The codimension-one non-étale locus of an actual affine morphism.  Unlike the
`UnnormalizedDynamics.nonEtaleLocus` field of the abstract dynamics, this set is defined directly from the
localized ring map. -/
def affineNonEtaleLocus (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Set (HeightOnePrime S) :=
  {q | ¬ Algebra.IsEtaleAt R q.1.asIdeal}

@[simp]
theorem mem_affineNonEtaleLocus_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : HeightOnePrime S) :
    q ∈ affineNonEtaleLocus R S ↔ ¬ Algebra.IsEtaleAt R q.1.asIdeal :=
  Iff.rfl

/-- On an affine scheme, the scheme-theoretic codimension-one carrier and the
height-one-prime carrier agree. -/
def affineDivisorPointEquiv (R : CommRingCat) :
    HeightOnePrime R ≃ SchemeDivisorPoint (AlgebraicGeometry.Spec R) where
  toFun p :=
    ⟨p.1, (AlgebraicGeometry.idealHeight_eq_coheight R p.1).symm.trans p.2⟩
  invFun x :=
    ⟨x.1, (AlgebraicGeometry.idealHeight_eq_coheight R x.1).trans x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying target point of a codimension-one source point.  This is deliberately
valued in all points of `Y`: for a finite map to a nonnormal target, preservation of
codimension one is a separate theorem rather than part of the definition. -/
def SchemeDivisorPoint.imagePoint {X Y : AlgebraicGeometry.Scheme}
    (f : X ⟶ Y) (x : SchemeDivisorPoint X) : Y :=
  f x.1

/-- Contraction of a height-one prime, regarded as a point of the whole target spectrum.
The target is not restricted to `HeightOnePrime R`, because a normalization comparison
must not silently assume height preservation over a nonnormal base. -/
def heightOneComapPoint {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Q : HeightOnePrime S) : PrimeSpectrum R :=
  PrimeSpectrum.comap (algebraMap R S) Q.1

section SchemeFibers

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f]

/-- A quasi-finite quasi-compact morphism has only finitely many codimension-one source
points above any target point.

This is the scheme-level finite-fiber fact needed for the map from divisors on a
normalization to points of the possibly nonnormal scheme.  No codimension assertion is
made about the target point; that separate assertion is exactly what is needed before the
target can be restricted to its divisor carrier. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.finite_divisorPoint_fiber (y : Y) :
    {x : SchemeDivisorPoint X | x.imagePoint f = y}.Finite := by
  let inclusion : SchemeDivisorPoint X → X := fun x => x.1
  have hfiber : (f ⁻¹' {y}).Finite := f.finite_preimage_singleton y
  change (inclusion ⁻¹' (f ⁻¹' {y})).Finite
  exact hfiber.preimage (Set.injOn_of_injective Subtype.val_injective)

end SchemeFibers

section NormalizationFibers

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.QuasiFinite R S]

/-- A quasi-finite affine morphism has only finitely many height-one primes above any
point of the target.

This is the finite-fiber input needed when comparing divisors on a possibly nonnormal
affine scheme with divisors on its normalization.  Notice that the target prime is not
assumed to have height one and the target ring is not assumed normal: this theorem only
restricts Mathlib's finite fiber on the full prime spectrum to the height-one primes of
the source. -/
theorem finite_heightOne_comap_fiber (p : PrimeSpectrum R) :
    {Q : HeightOnePrime S | heightOneComapPoint (R := R) Q = p}.Finite := by
  let inclusion : HeightOnePrime S → PrimeSpectrum S := fun Q => Q.1
  have hfiber :
      (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}).Finite :=
    Algebra.QuasiFinite.finite_comap_preimage_singleton p
  change (inclusion ⁻¹'
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})).Finite
  exact hfiber.preimage (Set.injOn_of_injective Subtype.val_injective)

end NormalizationFibers

section NonnormalTarget

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsDomain S] [Algebra.IsIntegral R S] [FaithfulSMul R S]

/-- A height-one prime downstairs has a height-one prime above it in an integral extension of
domains.

This direction does not require going down.  Incomparability shows that every prime strictly below
a chosen prime over `p` contracts strictly below `p`; since `p` has height one, that contraction is
zero, and integrality over a domain then makes the original prime zero. -/
theorem height_eq_one_of_liesOver_heightOne (P : Ideal S) (p : Ideal R)
    [P.IsPrime] [p.IsPrime] (hPp : P.LiesOver p) (hp : p.height = 1) :
    P.height = 1 := by
  have hle : P.height ≤ 1 := (Ideal.height_le_iff).mpr fun q hq hqP => by
    let _ : q.IsPrime := hq
    have hunder_lt : q.under R < P.under R := by
      obtain ⟨x, hxP, hxq⟩ := SetLike.exists_of_lt hqP
      exact Ideal.under_lt_under_of_integral_mem_sdiff hqP.le ⟨hxP, hxq⟩
        (Algebra.IsIntegral.isIntegral x)
    have hunder_lt_p : q.under R < p := by simpa [hPp.over] using hunder_lt
    have hunder_height : (q.under R).height < 1 :=
      (Ideal.height_le_iff.mp hp.le) (q.under R) inferInstance hunder_lt_p
    have hunder_bot : q.under R = ⊥ := by
      rw [Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at hunder_height
      exact hunder_height
    have hqbot : q = ⊥ := Ideal.eq_bot_of_under_eq_bot hunder_bot
    simp [hqbot]
  have hPne : P ≠ ⊥ := by
    intro hP
    have hpbot : p = ⊥ := by
      rw [hPp.over, hP]
      exact Ideal.under_bot R S
    exact Ideal.ne_bot_of_height_eq_one hp hpbot
  exact le_antisymm hle (by
    rw [Order.one_le_iff_ne_zero]
    exact Ideal.height_eq_zero_iff_eq_bot.not.mpr hPne)

/-- Contraction from normalized height-one primes to height-one primes of a possibly nonnormal
target, given precisely the missing codimension-preservation theorem. -/
noncomputable def heightOneUnderOfCodim
    (hcodim : ∀ Q : HeightOnePrime S, (Q.1.asIdeal.under R).height = 1) :
    HeightOnePrime S → HeightOnePrime R :=
  fun Q => ⟨PrimeSpectrum.comap (algebraMap R S) Q.1, hcodim Q⟩

/-- The explicitly codimension-preserving contraction map is surjective on divisors. -/
theorem heightOneUnderOfCodim_surjective
    (hcodim : ∀ Q : HeightOnePrime S, (Q.1.asIdeal.under R).height = 1) :
    Function.Surjective (heightOneUnderOfCodim (R := R) (S := S) hcodim) := by
  intro p
  obtain ⟨Q, hQ⟩ := comap_surjective_of_isIntegral_of_injective
    (fun x => Algebra.IsIntegral.isIntegral (R := R) x)
    (FaithfulSMul.algebraMap_injective R S) p.1
  have hQover : Q.asIdeal.LiesOver p.1.asIdeal :=
    ⟨(congr_arg PrimeSpectrum.asIdeal hQ).symm⟩
  have hQheight : Q.asIdeal.height = 1 :=
    height_eq_one_of_liesOver_heightOne Q.asIdeal p.1.asIdeal hQover p.2
  exact ⟨⟨Q, hQheight⟩, Subtype.ext hQ⟩

omit [IsDomain R] [IsDomain S] [Algebra.IsIntegral R S] [FaithfulSMul R S] in
/-- The explicitly codimension-preserving contraction map has finite fibers. -/
theorem finite_heightOneUnderOfCodim_fiber [Algebra.QuasiFinite R S]
    (hcodim : ∀ Q : HeightOnePrime S, (Q.1.asIdeal.under R).height = 1)
    (p : HeightOnePrime R) :
    (heightOneUnderOfCodim (R := R) (S := S) hcodim ⁻¹' {p}).Finite := by
  refine (finite_heightOne_comap_fiber (R := R) (S := S) p.1).subset ?_
  intro Q hQ
  change heightOneUnderOfCodim (R := R) (S := S) hcodim Q = p at hQ
  change heightOneComapPoint (R := R) Q = p.1
  exact congr_arg Subtype.val hQ

end NonnormalTarget

section Height

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain S] [IsIntegrallyClosed R]
  [Module.Finite R S] [FaithfulSMul R S]

/-- A finite injective extension of Noetherian domains, with normal base, preserves the
height of every prime under contraction.

The two inequalities come from going down and from the fact that a prime above `p` is
minimal over `pS`: integrality supplies minimality, while the quotient by `pS` makes its
height contribution zero. -/
theorem height_under_eq_of_finite_of_normal (P : Ideal S) [P.IsPrime] :
    (P.under R).height = P.height := by
  let p : Ideal R := P.under R
  let hp : p.IsPrime := Ideal.IsPrime.under R P
  let hPp : P.LiesOver p := ⟨rfl⟩
  let q : Ideal (S ⧸ p.map (algebraMap R S)) :=
    P.map (Ideal.Quotient.mk (p.map (algebraMap R S)))
  have hq : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa [p] using Ideal.map_comap_le)
  have hPmin : P ∈ (p.map (algebraMap R S)).minimalPrimes :=
    Ideal.IsIntegral.mem_minimalPrimes_map_under P
  rw [Ideal.minimalPrimes_eq_comap] at hPmin
  obtain ⟨q', hq'min, hq'⟩ := hPmin
  have hqq' : q = q' := by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [show q.comap (Ideal.Quotient.mk _) = P by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      apply sup_eq_left.mpr
      change (P.under R).map (algebraMap R S) ≤ P
      exact Ideal.map_comap_le]
    exact hq'.symm
  have hq0 : q.height = 0 := Ideal.height_eq_zero_iff.mpr (hqq' ▸ hq'min)
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  rw [show P.map (Ideal.Quotient.mk (p.map (algebraMap R S))) = q by rfl,
    hq0, add_zero] at hheight
  exact hheight.symm

/-- Contraction sends a height-one prime upstairs to a height-one prime downstairs. -/
noncomputable def heightOneUnder (Q : HeightOnePrime S) : HeightOnePrime R :=
  ⟨PrimeSpectrum.comap (algebraMap R S) Q.1,
    (height_under_eq_of_finite_of_normal Q.1.asIdeal).trans Q.2⟩

/-- The map on codimension-one points induced by the affine scheme morphism
`Spec S → Spec R`. -/
noncomputable def affineDivisorUnder :
    SchemeDivisorPoint (AlgebraicGeometry.Spec (CommRingCat.of S)) →
      SchemeDivisorPoint (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  fun Q => affineDivisorPointEquiv (CommRingCat.of R)
    (heightOneUnder (R := R) (S := S)
      ((affineDivisorPointEquiv (CommRingCat.of S)).symm Q))

@[simp]
theorem affineDivisorUnder_val (Q) :
    (affineDivisorUnder (R := R) (S := S) Q).1 =
      PrimeSpectrum.comap (algebraMap R S) Q.1 := rfl

/-- Lying over, restricted to codimension-one points.  This is the affine divisor version
of `DivisorDynamics.step_surjective`. -/
theorem heightOneUnder_surjective :
    Function.Surjective (heightOneUnder (R := R) (S := S)) := by
  intro p
  obtain ⟨Q, hQ⟩ := comap_surjective_of_isIntegral_of_injective
    (fun x => Algebra.IsIntegral.isIntegral (R := R) x)
    (FaithfulSMul.algebraMap_injective R S) p.1
  have hQheight : Q.asIdeal.height = 1 := by
    rw [← height_under_eq_of_finite_of_normal (R := R) Q.asIdeal]
    have hunder : Q.asIdeal.under R = p.1.asIdeal := by
      exact congr_arg PrimeSpectrum.asIdeal hQ
    rw [hunder, p.2]
  exact ⟨⟨Q, hQheight⟩, Subtype.ext hQ⟩

/-- Lying over for codimension-one points of the affine schemes themselves. -/
theorem affineDivisorUnder_surjective :
    Function.Surjective (affineDivisorUnder (R := R) (S := S)) :=
  (affineDivisorPointEquiv (CommRingCat.of R)).surjective.comp
    (heightOneUnder_surjective (R := R) (S := S) |>.comp
      (affineDivisorPointEquiv (CommRingCat.of S)).symm.surjective)

/-- The affine divisor pushforward along a finite normal map has finite fibers.

Together with `heightOneUnder_surjective`, this supplies the two set-theoretic properties
of the map on divisors used by the normalization bookkeeping. -/
theorem finite_heightOneUnder_fiber (p : HeightOnePrime R) :
    (heightOneUnder (R := R) (S := S) ⁻¹' {p}).Finite := by
  refine (finite_heightOne_comap_fiber (R := R) (S := S) p.1).subset ?_
  intro Q hQ
  change heightOneUnder (R := R) (S := S) Q = p at hQ
  change heightOneComapPoint (R := R) Q = p.1
  exact congr_arg Subtype.val hQ

end Height

section FiniteTypeHeight

variable (k : Type*) [Field k]
  {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra k R] [Algebra.FiniteType k R]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

include k

set_option linter.style.haveILetI false in
/-- A finite faithful extension of domains preserves prime height when the base is
of finite type over a field, even when that base is not normal.

Noether normalization supplies a finite injective polynomial subalgebra of `R`.
Both `R` and `S` are finite over that same normal polynomial ring, so the normal-base
height theorem applied twice gives the equality. -/
theorem height_under_eq_of_finite_of_finiteType (Q : Ideal S) [Q.IsPrime] :
    (Q.under R).height = Q.height := by
  obtain ⟨n, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin n) k
  letI : Algebra P R := φ.toRingHom.toAlgebra
  letI : Module.Finite P R := hfin
  letI : FaithfulSMul P R := (faithfulSMul_iff_algebraMap_injective P R).mpr hinj
  letI : Algebra P S := ((algebraMap R S).comp (algebraMap P R)).toAlgebra
  letI : IsScalarTower P R S := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite P S := Module.Finite.trans R S
  letI : FaithfulSMul P S := (faithfulSMul_iff_algebraMap_injective P S).mpr
    ((FaithfulSMul.algebraMap_injective R S).comp hinj)
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : (Q.under R).IsPrime := Ideal.IsPrime.under R Q
  calc
    (Q.under R).height = ((Q.under R).under P).height :=
      (height_under_eq_of_finite_of_normal (R := P) (S := R) (Q.under R)).symm
    _ = (Q.under P).height := by rw [Ideal.under_under]
    _ = Q.height := height_under_eq_of_finite_of_normal (R := P) Q

/-- Divisor contraction for a finite faithful extension of finite-type domains over a
field.  The target need not be normal; its codimension condition is proved above. -/
noncomputable def heightOneUnderOfFiniteType : HeightOnePrime S → HeightOnePrime R :=
  heightOneUnderOfCodim fun Q ↦
    (height_under_eq_of_finite_of_finiteType k Q.1.asIdeal).trans Q.2

@[simp]
theorem heightOneUnderOfFiniteType_val (Q : HeightOnePrime S) :
    (heightOneUnderOfFiniteType k Q).1 = heightOneComapPoint (R := R) Q :=
  rfl

/-- Every divisor downstairs has a divisor above it under finite faithful contraction
over a finite-type domain, with no normality assumption downstairs. -/
theorem heightOneUnderOfFiniteType_surjective :
    Function.Surjective (heightOneUnderOfFiniteType k (R := R) (S := S)) :=
  heightOneUnderOfCodim_surjective _

/-- Divisor contraction over a finite-type domain has finite fibers. -/
theorem finite_heightOneUnderOfFiniteType_fiber (p : HeightOnePrime R) :
    (heightOneUnderOfFiniteType k (S := S) ⁻¹' {p}).Finite :=
  finite_heightOneUnderOfCodim_fiber _ p

end FiniteTypeHeight

section LowDimensionalRegularLocal

open IsLocalRing Module

/-- A one-dimensional regular local ring is a domain.

This is the dimension-one case of Stacks Tag 00NP.  It is enough for the Step 0
Cartier argument below and avoids assuming the currently unavailable general theorem
that every regular local ring is a domain.  The proof writes the maximal ideal as
`(t)`, uses Krull intersection to write every nonzero element as a power of `t` times
a unit, and uses the positive dimension to rule out nilpotence of `t`. -/
theorem isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) : IsDomain R := by
  classical
  let m := maximalIdeal R
  have hfin : finrank (ResidueField R) (CotangentSpace R) = 1 := by
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hdim] at hreg
    exact_mod_cast hreg
  have hmprincipal : m.IsPrincipal :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hfin.le
  obtain ⟨t, ht⟩ := hmprincipal
  have hm_not_nil : ¬ IsNilpotent m := by
    intro hm
    let _ : IsArtinianRing R :=
      (isArtinianRing_iff_isNilpotent_maximalIdeal R).mpr hm
    have hzero : ringKrullDim R = 0 :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
        ((isArtinianRing_iff_krullDimLE_zero).mp inferInstance)
    rw [hdim] at hzero
    norm_num at hzero
  have ht_pow_ne : ∀ n : ℕ, t ^ n ≠ 0 := by
    intro n htn
    apply hm_not_nil
    refine ⟨n, ?_⟩
    rw [ht, Ideal.span_singleton_pow, htn]
    simp
  have hinter : ⨅ n : ℕ, m ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing m Ideal.IsPrime.ne_top'
  have hfactor : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = t ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, x ∉ m ^ n := by
      by_contra h
      push Not at h
      have hxinf : x ∈ ⨅ n : ℕ, m ^ n := by
        rw [Submodule.mem_iInf]
        exact h
      rw [hinter] at hxinf
      exact hx (by simpa using hxinf)
    have hN : x ∉ m ^ Nat.find hex := Nat.find_spec hex
    have hNpos : 0 < Nat.find hex := by
      by_contra h
      have hNzero : Nat.find hex = 0 := Nat.eq_zero_of_not_pos h
      apply hN
      simp [hNzero]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
    rw [hn] at hN
    have hxmem : x ∈ m ^ n := by
      exact Classical.not_not.mp (Nat.find_min hex (by omega))
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hxmem
    obtain ⟨u, hu⟩ := hxmem
    have hu_not_mem : u ∉ m := by
      intro hum
      apply hN
      rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rw [ht, Ideal.mem_span_singleton] at hum
      obtain ⟨v, rfl⟩ := hum
      refine ⟨v, ?_⟩
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hu
    have huunit : IsUnit u := by
      change u ∉ maximalIdeal R at hu_not_mem
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not]
        using hu_not_mem
    exact ⟨n, u, huunit, hu⟩
  let _ : NoZeroDivisors R := NoZeroDivisors.mk fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    obtain ⟨na, ua, hua, haeq⟩ := hfactor a ha
    obtain ⟨nb, ub, hub, hbeq⟩ := hfactor b hb
    exfalso
    have hpow : t ^ (na + nb) = 0 := by
      apply (hua.mul hub).mul_left_eq_zero.mp
      simpa [haeq, hbeq, pow_add, mul_assoc, mul_comm, mul_left_comm] using hab
    exact ht_pow_ne (na + nb) hpow
  exact NoZeroDivisors.to_isDomain R

/-- A one-dimensional regular local ring is a regular ring.

Mathlib's definition of `IsRegularRing` asks for regularity after localization at every
prime, while the library currently does not know the general theorem that a regular local
ring remains regular after localization.  In dimension one the preceding domain theorem
closes the gap: the cotangent-space criterion makes the ring a DVR, hence a Dedekind domain,
and Dedekind domains are regular rings. -/
theorem isRegularRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) : IsRegularRing R := by
  let _ : IsDomain R :=
    isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one R hdim
  have hfin : finrank (ResidueField R) (CotangentSpace R) = 1 := by
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hdim] at hreg
    exact_mod_cast hreg
  let _ : IsDiscreteValuationRing R :=
    IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfin
  let _ : IsDedekindDomain R :=
    ((IsDiscreteValuationRing.TFAE R (IsDiscreteValuationRing.not_isField R)).out 1 3).mp
      (inferInstance : IsDiscreteValuationRing R)
  infer_instance

/-- The exact low-dimensional local-factoriality statement needed in Step 0.

Let `R` be a two-dimensional regular local domain and `p` a height-one prime.  If
`R / p` is a one-dimensional regular local ring, then `p` is principal.  Geometrically,
`R` is the local ring of the regular ambient variety at the generic point of a divisor
of `B`, while `R / p` is the regular local ring of `B` there.

The proof first uses Nakayama to find an element of `p` outside `m²`.  Its cotangent
class extends to a basis of `m / m²`, so quotienting by that element leaves a
one-dimensional regular local ring.  The preceding dimension-one theorem makes that
quotient a domain, hence the element generates a prime ideal; height one then forces it
to equal `p`. -/
theorem heightOne_isPrincipal_of_regularLocalRing_dim_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (hdim : ringKrullDim R = 2) (p : Ideal R) [p.IsPrime]
    (hp : p.height = 1) [IsRegularLocalRing (R ⧸ p)]
    (hquotdim : ringKrullDim (R ⧸ p) = 1) : p.IsPrincipal := by
  classical
  let m := maximalIdeal R
  let q : R →+* R ⧸ p := Ideal.Quotient.mk p
  have hpm : p ≤ m := IsLocalRing.le_maximalIdeal_of_isPrime p
  have hfinR : finrank (ResidueField R) (CotangentSpace R) = 2 := by
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hdim] at hreg
    exact_mod_cast hreg
  have hfinQ : finrank (ResidueField (R ⧸ p)) (CotangentSpace (R ⧸ p)) = 1 := by
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace (R ⧸ p)).mp inferInstance
    rw [hquotdim] at hreg
    exact_mod_cast hreg
  have hp_not_sq : ¬ p ≤ m ^ 2 := by
    intro hp_sq
    have hprincipalQ : (maximalIdeal (R ⧸ p)).IsPrincipal :=
      IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hfinQ.le
    obtain ⟨yb, hyb⟩ := hprincipalQ
    have hybmem : yb ∈ maximalIdeal (R ⧸ p) := by
      rw [hyb]
      exact Ideal.mem_span_singleton_self yb
    have hmmap : m.map q = maximalIdeal (R ⧸ p) :=
      IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
    have hybmap : yb ∈ m.map q := hmmap.symm ▸ hybmem
    obtain ⟨y, hy, hyq⟩ :=
      (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hybmap
    have hmap_eq : m.map q = (Ideal.span {y}).map q := by
      rw [hmmap, hyb, Ideal.map_span, Set.image_singleton]
      exact congr_arg (fun z : R ⧸ p => Ideal.span {z}) hyq.symm
    have hcomap := congr_arg (Ideal.comap q) hmap_eq
    have hmsup : m ≤ Ideal.span {y} ⊔ p := by
      simpa [q, Ideal.comap_map_of_surjective, Ideal.mk_ker,
        sup_eq_left.mpr hpm, sup_comm] using hcomap.le
    have hpsmul : p ≤ m • (m : Submodule R R) := by
      simpa [smul_eq_mul, pow_two] using hp_sq
    have hnak : m ≤ Ideal.span {y} := by
      apply Submodule.le_of_le_smul_of_le_jacobson_bot m.fg_of_isNoetherianRing
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
      exact hmsup.trans (sup_le_sup_left hpsmul _)
    have hm_eq : m = Ideal.span {y} := le_antisymm hnak (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hy)
    have hmprincipal : m.IsPrincipal := ⟨y, hm_eq⟩
    have hle : finrank (ResidueField R) (CotangentSpace R) ≤ 1 :=
      IsLocalRing.finrank_cotangentSpace_le_one_iff.mpr hmprincipal
    omega
  obtain ⟨x, hxp, hx_sq⟩ := SetLike.not_le_iff_exists.mp hp_not_sq
  have hxm : x ∈ m := hpm hxp
  let x' : m := ⟨x, hxm⟩
  let xcot : CotangentSpace R := (maximalIdeal R).toCotangent x'
  have hxcot : xcot ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact hx_sq
  let L : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) {xcot}
  have hLne : L ≠ ⊤ := by
    intro hL
    have hprincipalTop : (⊤ : Submodule (ResidueField R) (CotangentSpace R)).IsPrincipal := by
      refine ⟨xcot, ?_⟩
      exact hL.symm
    have hle : finrank (ResidueField R) (CotangentSpace R) ≤ 1 :=
      Module.finrank_le_one_iff_top_isPrincipal.mpr hprincipalTop
    omega
  obtain ⟨ycot, -, hycot⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hLne)
  obtain ⟨y', hy'⟩ := (maximalIdeal R).toCotangent_surjective ycot
  let pair : Fin 2 → CotangentSpace R := ![ycot, xcot]
  have hpair : LinearIndependent (ResidueField R) pair := by
    rw [linearIndependent_fin2]
    refine ⟨hxcot, ?_⟩
    intro a ha
    apply hycot
    rw [show ycot = a • xcot by simpa [pair] using ha.symm]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton xcot))
  have hpair_span : Submodule.span (ResidueField R) (Set.range pair) = ⊤ :=
    hpair.span_eq_top_of_card_eq_finrank (by simpa using hfinR.symm)
  have hcospan : Submodule.span (ResidueField R)
      ((maximalIdeal R).toCotangent '' ({x', y'} : Set m)) = ⊤ := by
    rw [← hpair_span]
    congr 1
    ext z
    simp [pair, xcot, hy']
  have hmspan : Submodule.span R ({x', y'} : Set m) = ⊤ :=
    IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hcospan
  have hmxy : m = Ideal.span {x, (y' : R)} := by
    apply le_antisymm
    · intro z hz
      have hz' : (⟨z, hz⟩ : m) ∈ Submodule.span R ({x', y'} : Set m) := by
        rw [hmspan]
        trivial
      rw [Submodule.mem_span_pair] at hz'
      obtain ⟨a, b, hab⟩ := hz'
      rw [Ideal.mem_span_pair]
      exact ⟨a, b, congr_arg Subtype.val hab⟩
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · exact hxm
      · exact y'.2
  let I : Ideal R := Ideal.span {x}
  have hxne : x ≠ 0 := by
    intro hx0
    apply hx_sq
    rw [hx0]
    exact Submodule.zero_mem _
  have hxreg : IsSMulRegular R x := IsSMulRegular.of_ne_zero hxne
  have hIdim_eq : ringKrullDim (R ⧸ I) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hxm
  have hIle : I ≤ maximalIdeal R := by
    change Ideal.span {x} ≤ maximalIdeal R
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hxm
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have hIdim : ringKrullDim (R ⧸ I) = 1 := by
    have hnebot : ringKrullDim (R ⧸ I) ≠ ⊥ := by
      intro hbot
      have hsub : Subsingleton (R ⧸ I) := ringKrullDim_eq_bot_iff_subsingleton.mp hbot
      exact not_subsingleton_iff_nontrivial.mpr (inferInstance : Nontrivial (R ⧸ I)) hsub
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hnebot
    rw [hdim] at hIdim_eq
    rw [← hd] at hIdim_eq
    have hcoe : (↑(d + 1) : WithBot ℕ∞) = ↑(2 : ℕ∞) := by
      calc
        (↑(d + 1) : WithBot ℕ∞) = ↑d + ↑(1 : ℕ∞) := WithBot.coe_add d 1
        _ = ↑d + 1 := by rfl
        _ = 2 := hIdim_eq
        _ = ↑(2 : ℕ∞) := by rfl
    have hdadd : d + 1 = 2 := WithBot.coe_eq_coe.mp hcoe
    have hd1 : d = 1 := ENat.add_left_injective_of_ne_top ENat.one_ne_top (by
      simpa only [one_add_one_eq_two] using hdadd)
    exact hd.symm.trans (congr_arg ((↑) : ℕ∞ → WithBot ℕ∞) hd1)
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmaxI : maximalIdeal (R ⧸ I) = Ideal.span {Ideal.Quotient.mk I y'} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]
    have hmxy' : maximalIdeal R = Ideal.span {x, (y' : R)} := hmxy
    calc
      (maximalIdeal R).map (Ideal.Quotient.mk I) =
          (Ideal.span {x, (y' : R)}).map (Ideal.Quotient.mk I) :=
        congr_arg (fun J : Ideal R => J.map (Ideal.Quotient.mk I)) hmxy'
      _ = Ideal.span ((Ideal.Quotient.mk I) '' {x, (y' : R)}) :=
        Ideal.map_span _ _
      _ = Ideal.span {Ideal.Quotient.mk I y'} := by simp [I]
  have hmaxI_le : (maximalIdeal (R ⧸ I)).spanFinrank ≤ 1 := by
    rw [hmaxI]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton _)).trans_eq
      (Set.ncard_singleton _)
  let _ : IsRegularLocalRing (R ⧸ I) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R ⧸ I) (by
      rw [hIdim]
      exact_mod_cast hmaxI_le)
  let _ : IsDomain (R ⧸ I) :=
    isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one (R ⧸ I) hIdim
  have hIprime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  have hxprime : Prime x := (Ideal.span_singleton_prime hxne).mp hIprime
  exact ⟨x, Ideal.eq_span_singleton_of_height_eq_one hp hxp hxprime⟩

end LowDimensionalRegularLocal

section LocalRings

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
  [IsIntegrallyClosed R]

/-- The local ring at a height-one prime of a Noetherian normal domain is a DVR.

This is the affine form of the standard divisor fact used when the paper defines
ramification indices.  The proof does not assume factoriality: primes of `Rₚ` correspond
to primes of `R` below `p`, and height one says that the only nonzero one is `p` itself. -/
theorem isDiscreteValuationRing_localizationAtPrime_of_heightOne
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let Rp := Localization.AtPrime p
  have hnormal : IsIntegrallyClosed Rp :=
    isIntegrallyClosed_of_isLocalization Rp p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  have hnotfield : ¬ IsField Rp :=
      (IsLocalRing.isField_iff_maximalIdeal_eq (R := Rp)).not.mpr <| by
    intro hmax
    apply p.ne_bot_of_height_eq_one hp
    rw [← Localization.AtPrime.under_maximalIdeal (I := p), hmax]
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective (S := Rp) p.primeCompl_le_nonZeroDivisors)
  change IsDiscreteValuationRing Rp
  apply ((IsDiscreteValuationRing.TFAE Rp hnotfield).out 4 1).mp
  constructor
  · exact hnormal
  refine ⟨IsLocalRing.maximalIdeal Rp,
    ⟨(IsLocalRing.isField_iff_maximalIdeal_eq (R := Rp)).not.mp hnotfield,
      inferInstance⟩, ?_⟩
  intro P hP
  let q : Ideal R := P.under R
  let _ : P.IsPrime := hP.2
  let _ : q.IsPrime := Ideal.IsPrime.under R P
  have hdisjoint : Disjoint (p.primeCompl : Set R) q :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint p.primeCompl Rp P).mp hP.2).2
  have hqp : q ≤ p := by
    intro x hxq
    by_contra hxp
    exact Set.disjoint_left.mp hdisjoint hxp hxq
  have hqne : q ≠ ⊥ := by
    intro hq
    apply hP.1
    have hunder : P.under R = ⊥ := by simpa [q] using hq
    calc
      P = Ideal.map (algebraMap R Rp) (P.under R) :=
        (IsLocalization.map_under p.primeCompl Rp P).symm
      _ = Ideal.map (algebraMap R Rp) ⊥ := congr_arg _ hunder
      _ = ⊥ := Ideal.map_bot
  have hqp_eq : q = p := by
    apply le_antisymm hqp
    by_contra hpq
    have hne : q ≠ p := fun h => hpq (h ▸ le_rfl)
    have hlt : q < p := lt_of_le_of_ne hqp hne
    have hheight := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hp, ENat.add_one_le_iff' ENat.one_ne_top, Order.lt_one_iff,
      Ideal.height_eq_zero_iff_eq_bot] at hheight
    exact hqne hheight
  exact (Localization.AtPrime.eq_maximalIdeal_iff_under_eq (I := p)).mp hqp_eq

/-- The local ring at a height-one prime represented by `HeightOnePrime` is a DVR. -/
theorem heightOnePrime_localRing_isDiscreteValuationRing (p : HeightOnePrime R) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) :=
  isDiscreteValuationRing_localizationAtPrime_of_heightOne p.1.asIdeal p.2

/-- A two-dimensional normal regular local domain is a regular ring.

This is the other low-dimensional localization result needed to use the local ring at the
generic point of a divisor in the bounding argument.  The general theorem "regular local
implies regular" is absent from Mathlib, but in dimension two normality suffices: the
generic localization is a field, the maximal localization is the original regular local
ring, and every remaining prime has height one, where normality makes its localization a
DVR. -/
theorem isRegularRing_of_isRegularLocalRing_of_isIntegrallyClosed_dim_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R = 2) : IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p hp
  by_cases hpbot : p = ⊥
  · subst p
    let _ : Field (Localization.AtPrime (⊥ : Ideal R)) := IsField.toField <| by
      simp [IsLocalRing.isField_iff_maximalIdeal_eq,
        ← Localization.AtPrime.map_eq_maximalIdeal]
    infer_instance
  by_cases hpmax : p = IsLocalRing.maximalIdeal R
  · subst p
    let e : R ≃ₐ[R] Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
      IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
        (fun x ↦ by simpa using! fun a ↦ a)
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv
  have hp_lt : p < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p) hpmax
  have hbot_lt : (⊥ : Ideal R) < p := bot_lt_iff_ne_bot.mpr hpbot
  have hpos : 0 < p.height := by
    simpa using Ideal.height_strict_mono_of_isPrime_of_isPrime hbot_lt
  have hle : p.height ≤ 1 := by
    have h := Ideal.height_strict_mono_of_isPrime_of_isPrime hp_lt
    have hmaxheight : (IsLocalRing.maximalIdeal R).height = (2 : ℕ∞) :=
      WithBot.coe_eq_coe.mp (IsLocalRing.maximalIdeal_height_eq_ringKrullDim.trans hdim)
    rw [hmaxheight] at h
    simpa using h
  have hpheight : p.height = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr (ne_of_gt hpos))
  let _ : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne p hpheight
  infer_instance

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- If a prime ideal becomes principal in the local ring at a larger prime, then it is
principal after mapping to any realization of a suitable principal localization.

This is the algebraic shrinking step needed in Step 0 of the bounding theorem.  Applied
after local factoriality makes `p R_q` principal, it produces one equation for the divisor
on an actual affine neighborhood of `q`.  Quantifying over the realization of the
localization lets the result apply directly to section rings of affine basic opens. -/
theorem exists_principal_map_of_atPrime_isPrincipal
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    [(p.map (algebraMap R (Localization.AtPrime q))).IsPrincipal] :
    ∃ a f : R, a ∈ p ∧ f ∉ q ∧
      ∀ (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.Away f T],
        p.map (algebraMap R T) = Ideal.span {algebraMap R T a} := by
  let Rq := Localization.AtPrime q
  let π := Submodule.IsPrincipal.generator (p.map (algebraMap R Rq))
  obtain ⟨a, s, hπ⟩ := IsLocalization.exists_mk'_eq q.primeCompl π
  have hlocal : p.map (algebraMap R Rq) = Ideal.span {algebraMap R Rq a} := by
    rw [← Submodule.IsPrincipal.span_singleton_generator (p.map (algebraMap R Rq))]
    change Ideal.span {π} = _
    rw [← hπ, ← Ideal.span_singleton_mul_right_unit (IsLocalization.map_units Rq s)]
    rw [IsLocalization.mk'_spec]
  have ha : a ∈ p := by
    have ha' : algebraMap R Rq a ∈ p.map (algebraMap R Rq) := by
      rw [hlocal]
      exact Ideal.mem_span_singleton_self _
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl] at ha'
    obtain ⟨m, hm, hma⟩ := ha'
    apply ((show p.IsPrime from inferInstance).mem_or_mem hma).resolve_left
    exact fun hmp => hm (hpq hmp)
  obtain ⟨n, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp p.fg_of_isNoetherianRing
  have hden : ∀ i : Fin n, ∃ t : q.primeCompl, (t : R) * g i ∈ Ideal.span {a} := by
    intro i
    have hgi : g i ∈ p := by
      rw [← hg]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hmap : algebraMap R Rq (g i) ∈ (Ideal.span {a}).map (algebraMap R Rq) := by
      rw [Ideal.map_span, Set.image_singleton, ← hlocal]
      exact Ideal.mem_map_of_mem _ hgi
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl] at hmap
    obtain ⟨t, ht, htg⟩ := hmap
    exact ⟨⟨t, ht⟩, htg⟩
  choose t ht using hden
  let f : R := ∏ i, (t i : R)
  have hf : f ∉ q := by
    intro hfp
    rw [show f = ∏ i ∈ Finset.univ, (t i : R) by simp [f],
      Ideal.IsPrime.prod_mem_iff] at hfp
    obtain ⟨i, _, hi⟩ := hfp
    exact (t i).2 hi
  refine ⟨a, f, ha, hf, ?_⟩
  intro T _ _ _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, ← hg, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hti_unit : IsUnit (algebraMap R T (t i : R)) := by
      have hfu : IsUnit (algebraMap R T f) :=
        IsLocalization.Away.algebraMap_isUnit f
      have hfac : ∃ z : R, f = (t i : R) * z := by
        refine ⟨∏ j ∈ Finset.univ.erase i, (t j : R), ?_⟩
        simpa [f, mul_comm] using
          (Finset.prod_erase_mul Finset.univ (fun j => (t j : R))
            (Finset.mem_univ i)).symm
      obtain ⟨z, hz⟩ := hfac
      have heq : algebraMap R T f =
          algebraMap R T (t i : R) * algebraMap R T z := by
        rw [hz, map_mul]
      exact isUnit_of_mul_isUnit_left (heq ▸ hfu)
    change algebraMap R T (g i) ∈ Ideal.span {algebraMap R T a}
    apply (Ideal.unit_mul_mem_iff_mem _ hti_unit).mp
    rw [← map_mul]
    have htgmap : algebraMap R T ((t i : R) * g i) ∈
        (Ideal.span {a}).map (algebraMap R T) :=
      Ideal.mem_map_of_mem _ (ht i)
    rwa [Ideal.map_span, Set.image_singleton] at htgmap
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ha

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- Canonical-localization specialization of
`exists_principal_map_of_atPrime_isPrincipal`. -/
theorem exists_principal_localizationAway_of_atPrime_isPrincipal
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    [(p.map (algebraMap R (Localization.AtPrime q))).IsPrincipal] :
    ∃ a f : R, a ∈ p ∧ f ∉ q ∧
      p.map (algebraMap R (Localization.Away f)) =
        Ideal.span {algebraMap R (Localization.Away f) a} := by
  obtain ⟨a, f, ha, hf, h⟩ :=
    exists_principal_map_of_atPrime_isPrincipal p q hpq
  exact ⟨a, f, ha, hf, h (Localization.Away f)⟩

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- At a codimension-two regular point, the localized height-one divisor ideal has one
generator.

Unlike the subsequent denominator-clearing theorem, this stays in the local ring at the
chosen point. It is therefore the direct source of the equation used by
`LocalBoundingChart`. -/
theorem exists_generator_map_atPrime_regular_dim_two
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p.height = 1)
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = 2)
    [IsRegularLocalRing
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))]
    (hquotdim : ringKrullDim
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) = 1) :
    ∃ a : Localization.AtPrime q,
      p.map (algebraMap R (Localization.AtPrime q)) = Ideal.span {a} := by
  let Rq := Localization.AtPrime q
  let P : Ideal Rq := p.map (algebraMap R Rq)
  have hd : Disjoint (q.primeCompl : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    exact fun x hxq hxp => hxq (hpq hxp)
  let _ : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Rq p inferInstance hd
  have hheight : P.height = 1 :=
    (IsLocalization.height_map_of_disjoint q.primeCompl p hd).trans hp
  let _ : P.IsPrincipal :=
    heightOne_isPrincipal_of_regularLocalRing_dim_two Rq hdim P hheight hquotdim
  exact ⟨Submodule.IsPrincipal.generator P,
    (Submodule.IsPrincipal.span_singleton_generator P).symm⟩

/-- In a domain, a height-one prime containing a nonzero element is minimal over the
principal ideal generated by that element.

This is the component-selection fact used by the local bounding chart.  A prime strictly
below the chosen height-one prime has height zero, hence is the zero ideal; it therefore
cannot contain the nonzero equation. -/
theorem mem_minimalPrimes_span_singleton_of_height_eq_one
    {T : Type*} [CommRing T] [IsDomain T]
    {b : T} {P : Ideal T} [P.IsPrime]
    (hb : b ≠ 0) (hbP : b ∈ P) (hP : P.height = 1) :
    P ∈ (Ideal.span {b}).minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbP)⟩, ?_⟩
  intro Q hQ hQP
  by_contra hnot
  have hlt : Q < P := lt_of_le_of_ne hQP (by
    intro h
    apply hnot
    rw [h])
  have hQheight : Q.height < 1 :=
    (Ideal.height_le_iff.mp hP.le) Q hQ.1 hlt
  have hQbot : Q = ⊥ := by
    rw [Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at hQheight
    exact hQheight
  apply hb
  have hbQ : b ∈ Q := hQ.2 (Ideal.mem_span_singleton_self b)
  simpa [hQbot] using hbQ

omit [IsIntegrallyClosed R] in
/-- Step 0 local principality without the full regular-local-UFD theorem.

At the chosen point of the manuscript, the ambient local ring has dimension two and the
local ring of the divisor has dimension one.  If both are regular, the preceding
low-dimensional theorem makes the localized height-one prime principal.  The denominator-
clearing theorem then spreads its generator to a principal-open affine neighborhood.

This is strictly narrower than Stacks 0AG0/0AGA, but it is exactly the case used in the
proof of `thm:bounding`. -/
theorem exists_principal_localizationAway_of_atPrime_regular_dim_two
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p.height = 1)
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = 2)
    [IsRegularLocalRing
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))]
    (hquotdim : ringKrullDim
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) = 1) :
    ∃ a f : R, a ∈ p ∧ f ∉ q ∧
      p.map (algebraMap R (Localization.Away f)) =
        Ideal.span {algebraMap R (Localization.Away f) a} := by
  let Rq := Localization.AtPrime q
  let P : Ideal Rq := p.map (algebraMap R Rq)
  have hd : Disjoint (q.primeCompl : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    exact fun x hxq hxp => hxq (hpq hxp)
  let _ : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Rq p inferInstance hd
  have hheight : P.height = 1 :=
    (IsLocalization.height_map_of_disjoint q.primeCompl p hd).trans hp
  let _ : P.IsPrincipal :=
    heightOne_isPrincipal_of_regularLocalRing_dim_two Rq hdim P hheight hquotdim
  exact exists_principal_localizationAway_of_atPrime_isPrincipal p q hpq

omit [IsIntegrallyClosed R] in
/-- If the local ring at `q` is a UFD, a height-one prime `p ⊆ q` is cut out by one
equation on a principal-open neighborhood of `q`.

This isolates the exact use of Stacks 0AG0/0AGA in Step 0: once regular-local ⇒ UFD is
available, the remaining passage from the local generator to an affine neighborhood is
the preceding theorem. -/
theorem exists_principal_localizationAway_of_atPrime_ufd
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p.height = 1)
    [UniqueFactorizationMonoid (Localization.AtPrime q)] :
    ∃ a f : R, a ∈ p ∧ f ∉ q ∧
      p.map (algebraMap R (Localization.Away f)) =
        Ideal.span {algebraMap R (Localization.Away f) a} := by
  have hd : Disjoint (q.primeCompl : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    exact fun x hxq hxp => hxq (hpq hxp)
  let _ : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl
      (Localization.AtPrime q) p inferInstance hd
  have hheight : (p.map (algebraMap R (Localization.AtPrime q))).height = 1 :=
    (IsLocalization.height_map_of_disjoint q.primeCompl p hd).trans hp
  let _ : (p.map (algebraMap R (Localization.AtPrime q))).IsPrincipal :=
    UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight
  exact exists_principal_localizationAway_of_atPrime_isPrincipal p q hpq

/-- A height-one prime on a Noetherian normal affine scheme is principal after shrinking
to a principal open neighborhood of its generic point.

The proof uses the DVR at the prime to obtain a local generator, then clears the finitely
many denominators needed for a generating family of the prime.  This treats the generic
point itself; Step 0 needs the more general preceding theorem at a point lying on the
divisor, together with local factoriality there. -/
theorem exists_principal_localizationAway_of_heightOne
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ a f : R, a ∈ p ∧ f ∉ p ∧
      p.map (algebraMap R (Localization.Away f)) =
        Ideal.span {algebraMap R (Localization.Away f) a} := by
  let Rp := Localization.AtPrime p
  let _ : IsDiscreteValuationRing Rp :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne p hp
  let _ : (p.map (algebraMap R Rp)).IsPrincipal := inferInstance
  exact exists_principal_localizationAway_of_atPrime_isPrincipal p p le_rfl

end LocalRings

section Ramification

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Mathlib's ramification index at a height-one prime. -/
noncomputable def heightOneRamificationIdx (Q : HeightOnePrime S) : ℕ :=
  Ideal.ramificationIdx Q.1.asIdeal R

/-- The ramification index at a height-one prime is positive. -/
theorem heightOneRamificationIdx_pos (Q : HeightOnePrime S) :
    0 < heightOneRamificationIdx (R := R) Q := by
  have := Q.1.isPrime
  exact Ideal.ramificationIdx_pos (R := R) Q.1.asIdeal

omit [Module.Finite R S] in
/-- Ramification indices at codimension-one primes multiply in a tower when the
localized upper extension is flat.  This is the geometric tower identity behind
the product used by `DivisorDynamics.iterateRamificationIdx`; unlike that product identity, this theorem
is about Mathlib's actual local ramification index. -/
theorem heightOneRamificationIdx_tower {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (Q : HeightOnePrime S) (P : HeightOnePrime T)
    [P.1.asIdeal.LiesOver Q.1.asIdeal]
    [Algebra (Localization.AtPrime Q.1.asIdeal)
      (Localization.AtPrime P.1.asIdeal)]
    [IsScalarTower S (Localization.AtPrime Q.1.asIdeal)
      (Localization.AtPrime P.1.asIdeal)]
    [Module.Flat (Localization.AtPrime Q.1.asIdeal)
      (Localization.AtPrime P.1.asIdeal)] :
    heightOneRamificationIdx (R := R) P =
      heightOneRamificationIdx (R := R) Q * heightOneRamificationIdx (R := S) P :=
  Ideal.ramificationIdx_tower' Q.1.asIdeal P.1.asIdeal

/-- The codimension-one branch support as contracted target ideals.

This unbundled form does not require proving in advance that every contraction has height
one.  Under the normal finite hypotheses below, `heightOneBranch` is its height-one-prime
refinement. -/
def heightOneBranchIdeal : Set (Ideal R) :=
  (fun Q : HeightOnePrime S => Q.1.asIdeal.under R) ''
    {Q : HeightOnePrime S | 1 < heightOneRamificationIdx (R := R) Q}

omit [Module.Finite R S] in
/-- Support of the contracted branch ideals on `D` implies that every ramified source
divisor contains the pullback of `D`. -/
theorem ramified_heightOne_lies_over_of_branchIdeal_subset_singleton
    (D : Ideal R)
    (hbranch : heightOneBranchIdeal (R := R) (S := S) ⊆ {D})
    (Q : HeightOnePrime S) (hQ : 1 < heightOneRamificationIdx (R := R) Q) :
    D.map (algebraMap R S) ≤ Q.1.asIdeal := by
  have hmem : Q.1.asIdeal.under R ∈
      heightOneBranchIdeal (R := R) (S := S) := ⟨Q, hQ, rfl⟩
  have heq : Q.1.asIdeal.under R = D := by
    simpa using hbranch hmem
  rw [← heq]
  exact Ideal.map_comap_le

end Ramification

section RamificationDVR

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain S] [IsIntegrallyClosed R]
  [IsIntegrallyClosed S] [Module.Finite R S] [FaithfulSMul R S]

/-- At a height-one prime `Q`, the extension of the contracted prime to the DVR `S_Q`
is a power of its maximal ideal. -/
theorem exists_heightOneDvrExponent (Q : HeightOnePrime S) :
    ∃ n : ℕ,
      (Q.1.asIdeal.under R).map
          (algebraMap R (Localization.AtPrime Q.1.asIdeal)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q.1.asIdeal) ^ n := by
  let _ : IsDomain R := Function.Injective.isDomain (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S)
  let Sq := Localization.AtPrime Q.1.asIdeal
  let _ : IsDiscreteValuationRing Sq :=
    heightOnePrime_localRing_isDiscreteValuationRing Q
  let _ : FaithfulSMul R Sq := FaithfulSMul.trans R S Sq
  have hpheight : (Q.1.asIdeal.under R).height = 1 :=
    (height_under_eq_of_finite_of_normal Q.1.asIdeal).trans Q.2
  have hpne : Q.1.asIdeal.under R ≠ ⊥ :=
    Ideal.ne_bot_of_height_eq_one hpheight
  exact exists_maximalIdeal_pow_eq_of_principal Sq inferInstance
    ((Q.1.asIdeal.under R).map (algebraMap R Sq)) (Ideal.map_ne_bot_of_ne_bot hpne)

/-- The exponent of the contracted height-one prime in the maximal ideal of the DVR
`S_Q`.  This is the usual valuation-theoretic ramification exponent. -/
noncomputable def heightOneDvrExponent (Q : HeightOnePrime S) : ℕ :=
  Nat.find (exists_heightOneDvrExponent (R := R) Q)

/-- The defining factorization for `heightOneDvrExponent`. -/
theorem heightOneDvrExponent_spec (Q : HeightOnePrime S) :
    (Q.1.asIdeal.under R).map
        (algebraMap R (Localization.AtPrime Q.1.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q.1.asIdeal) ^
        heightOneDvrExponent (R := R) Q :=
  Nat.find_spec (exists_heightOneDvrExponent (R := R) Q)

/-- Mathlib's length-theoretic ramification index is exactly the usual DVR exponent at a
height-one prime. -/
theorem heightOneRamificationIdx_eq_dvrExponent (Q : HeightOnePrime S) :
    heightOneRamificationIdx (R := R) Q = heightOneDvrExponent (R := R) Q := by
  let Sq := Localization.AtPrime Q.1.asIdeal
  let _ : IsDiscreteValuationRing Sq :=
    heightOnePrime_localRing_isDiscreteValuationRing Q
  rw [heightOneRamificationIdx, Ideal.ramificationIdx_def]
  change (Module.length Sq
    (Sq ⧸ (Q.1.asIdeal.under R).map (algebraMap R Sq))).toNat = _
  rw [heightOneDvrExponent_spec (R := R) Q,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

end RamificationDVR

section BranchSupport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain S]
  [IsIntegrallyClosed R]
  [Module.Finite R S] [FaithfulSMul R S]

/-- The branch set of a finite dominant normal affine map on codimension-one points.

A target divisor belongs to this set exactly when some source divisor above it has
ramification index greater than one.  This is the two-ring analogue of `DivisorDynamics.branch`.
-/
def heightOneBranch : Set (HeightOnePrime R) :=
  heightOneUnder (R := R) (S := S) ''
    {Q : HeightOnePrime S | 1 < heightOneRamificationIdx (R := R) Q}

theorem mem_heightOneBranch_iff (D : HeightOnePrime R) :
    D ∈ heightOneBranch (R := R) (S := S) ↔
      ∃ Q : HeightOnePrime S,
        1 < heightOneRamificationIdx (R := R) Q ∧
          heightOneUnder (R := R) (S := S) Q = D :=
  Iff.rfl

/-- Support of the honest height-one branch set on `D` implies the corresponding
support statement for the unbundled contracted ideals.

This is the exact conversion needed by the local chart constructor: under the finite
normal hypotheses, `heightOneUnder` proves that every contracted ramified prime is again
height one, so forgetting the height proof loses no support information. -/
theorem heightOneBranchIdeal_subset_singleton_of_heightOneBranch_subset_singleton
    (D : HeightOnePrime R)
    (hbranch : heightOneBranch (R := R) (S := S) ⊆ {D}) :
    heightOneBranchIdeal (R := R) (S := S) ⊆ {D.1.asIdeal} := by
  rintro E ⟨Q, hQ, rfl⟩
  have hmem : heightOneUnder (R := R) (S := S) Q ∈
      heightOneBranch (R := R) (S := S) := ⟨Q, hQ, rfl⟩
  have heq : heightOneUnder (R := R) (S := S) Q = D := by
    simpa using hbranch hmem
  simpa [heightOneUnder] using
    congr_arg (fun Z : HeightOnePrime R => Z.1.asIdeal) heq

/-- If the codimension-one branch set is supported on one target divisor `D`, every
ramified height-one source prime contains the pullback of the ideal of `D`.

This converts the manuscript's support inclusion `Branch(f|_U) ⊆ D` into the exact
ring-theoretic premise used by the canonical local-chart constructor. -/
theorem ramified_heightOne_lies_over_of_branch_subset_singleton
    (D : HeightOnePrime R)
    (hbranch : heightOneBranch (R := R) (S := S) ⊆ {D})
    (Q : HeightOnePrime S) (hQ : 1 < heightOneRamificationIdx (R := R) Q) :
    D.1.asIdeal.map (algebraMap R S) ≤ Q.1.asIdeal := by
  have hmem : heightOneUnder (R := R) (S := S) Q ∈
      heightOneBranch (R := R) (S := S) :=
    ⟨Q, hQ, rfl⟩
  have heq : heightOneUnder (R := R) (S := S) Q = D := by
    simpa using hbranch hmem
  have hunder : Q.1.asIdeal.under R = D.1.asIdeal := by
    exact congr_arg (fun E : HeightOnePrime R => E.1.asIdeal) heq
  rw [← hunder]
  exact Ideal.map_comap_le

/-- Pointed form of branch avoidance.

It is enough that the selected point `q` lie on no branch divisor other than `D`:
then every ramified source divisor whose contraction passes through `q` contains the
pullback of `D`.  This is the exact implication supplied by the open chosen in Step 0;
it does not require the branch locus on the whole affine chart to be a singleton. -/
theorem ramified_heightOne_lies_over_of_avoids_other_branch_at
    (q : Ideal R) (D : HeightOnePrime R)
    (havoid : ∀ E ∈ heightOneBranch (R := R) (S := S), E ≠ D →
      ¬ E.1.asIdeal ≤ q)
    (Q : HeightOnePrime S) (hQ : 1 < heightOneRamificationIdx (R := R) Q)
    (hQq : Q.1.asIdeal.under R ≤ q) :
    D.1.asIdeal.map (algebraMap R S) ≤ Q.1.asIdeal := by
  let E : HeightOnePrime R := heightOneUnder (R := R) (S := S) Q
  have hEbranch : E ∈ heightOneBranch (R := R) (S := S) := ⟨Q, hQ, rfl⟩
  have hEq : E = D := by
    by_contra hne
    apply (havoid E hEbranch hne)
    simpa [E, heightOneUnder] using hQq
  have hunder : Q.1.asIdeal.under R = D.1.asIdeal := by
    simpa [E, heightOneUnder] using
      congr_arg (fun F : HeightOnePrime R ↦ F.1.asIdeal) hEq
  rw [← hunder]
  exact Ideal.map_comap_le

end BranchSupport

section Finiteness

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain S]
  [Algebra.FinitePresentation R S] [IsNoetherianRing S]

/-- If the finite-presentation map is generically étale, only finitely many height-one
primes have ramification index greater than one. -/
theorem finite_heightOne_ramified
    (hgen : nonEtaleLocus R S ≠ Set.univ) :
    {Q : HeightOnePrime S | 1 < heightOneRamificationIdx (R := R) Q}.Finite := by
  let E : Set (PrimeSpectrum S) := nonEtaleLocus R S
  have hEclosed : IsClosed E := isClosed_nonEtaleLocus R S
  let I : Ideal S := PrimeSpectrum.vanishingIdeal E
  have hzero : PrimeSpectrum.zeroLocus (I : Set S) = E := by
    change PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal E : Set S) = E
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hEclosed.closure_eq]
  have hIne : I ≠ ⊥ := by
    intro hI
    apply hgen
    change E = Set.univ
    rw [← hzero, hI, PrimeSpectrum.zeroLocus_bot]
  apply Set.Finite.of_finite_image (f := fun Q : HeightOnePrime S => Q.1.asIdeal) _
  · intro Q _ Q' _ h
    exact Subtype.ext (PrimeSpectrum.ext h)
  refine I.finite_minimalPrimes_of_isNoetherianRing.subset ?_
  rintro q ⟨Q, hQram, rfl⟩
  have hQE : Q.1 ∈ E :=
    mem_nonEtaleLocus_of_one_lt_ramificationIdx R S Q.1 hQram
  have hIQ : I ≤ Q.1.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus Q.1 (I : Set S)).mp (hzero.symm ▸ hQE)
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hIQ
  have hpne : p ≠ ⊥ := fun hp0 => hIne (bot_unique (hp0 ▸ hp.le))
  have hqheight : Q.1.asIdeal.height = 1 := Q.2
  have hpqeq : p = Q.1.asIdeal := by
    apply eq_of_le_of_not_lt hpq
    intro hpq'
    have := hp.isPrime
    have hheight := Ideal.height_add_one_le_of_lt_of_isPrime hpq'
    rw [hqheight, ENat.add_one_le_iff' ENat.one_ne_top, Order.lt_one_iff,
      Ideal.height_eq_zero_iff_eq_bot] at hheight
    exact hpne hheight
  simpa [hpqeq] using hp

end Finiteness

section SelfMap

/- The usual self-actions have higher instance priority than the actions induced by a
nonidentity ring endomorphism.  Inside this section the algebra structure is the chosen
self-map, not `Algebra.id`. -/
attribute [-instance] Algebra.id instSMulOfMul Semiring.toModule

variable {R : Type*} [CommRing R] [Algebra R R] [IsNoetherianRing R]
  [IsDomain R] [IsIntegrallyClosed R] [Module.Finite R R]
  [FaithfulSMul R R] [Algebra.FinitePresentation R R]

/-- The divisorial dynamics induced by a finite injective endomorphism of a normal
Noetherian domain, expressed by a nonidentity `Algebra R R` structure.

Its carrier is the height-one spectrum, its step is contraction, and its ramification
function is Mathlib's `Ideal.ramificationIdx`.  Thus `step_surjective`, positivity, and
finiteness of the branch set are theorems rather than supplied fields. -/
noncomputable def divisorDynamicsOfFiniteNormalSelfAlgebra
    (hgen : nonEtaleLocus R R ≠ Set.univ) :
    DivisorDynamics (HeightOnePrime R) := by
  let step : HeightOnePrime R → HeightOnePrime R :=
    heightOneUnder (R := R) (S := R)
  let ram : HeightOnePrime R → ℕ := heightOneRamificationIdx (R := R)
  refine
    { step := step
      ramificationIdx := ram
      ramificationIdx_pos := ?_
      step_surjective := ?_
      step_image_ramified_finite := ?_ }
  · exact heightOneRamificationIdx_pos (R := R)
  · exact heightOneUnder_surjective (R := R) (S := R)
  · refine ((finite_heightOne_ramified (R := R) (S := R) hgen).image step).subset ?_
    rintro Q ⟨Q', hstep, hram⟩
    exact ⟨Q', hram, hstep⟩

@[simp]
theorem divisorDynamicsOfFiniteNormalSelfAlgebra_step
    (hgen : nonEtaleLocus R R ≠ Set.univ) (Q : HeightOnePrime R) :
    (divisorDynamicsOfFiniteNormalSelfAlgebra hgen).step Q =
      heightOneUnder (R := R) (S := R) Q :=
  rfl

@[simp]
theorem divisorDynamicsOfFiniteNormalSelfAlgebra_ramificationIdx
    (hgen : nonEtaleLocus R R ≠ Set.univ) (Q : HeightOnePrime R) :
    (divisorDynamicsOfFiniteNormalSelfAlgebra hgen).ramificationIdx Q = heightOneRamificationIdx (R := R) Q :=
  rfl

/-- The abstract branch set of the canonical affine divisor dynamics is exactly the
honest height-one branch set of the ring endomorphism. -/
theorem divisorDynamicsOfFiniteNormalSelfAlgebra_branch
    (hgen : nonEtaleLocus R R ≠ Set.univ) :
    (divisorDynamicsOfFiniteNormalSelfAlgebra hgen).branch =
      heightOneBranch (R := R) (S := R) := by
  ext D
  simp only [DivisorDynamics.mem_branch_iff, divisorDynamicsOfFiniteNormalSelfAlgebra_step,
    divisorDynamicsOfFiniteNormalSelfAlgebra_ramificationIdx, mem_heightOneBranch_iff]
  constructor
  · rintro ⟨Q, hQD, hQ⟩
    exact ⟨Q, hQ, hQD⟩
  · rintro ⟨Q, hQ, hQD⟩
    exact ⟨Q, hQD, hQ⟩

end SelfMap

end Pcf
