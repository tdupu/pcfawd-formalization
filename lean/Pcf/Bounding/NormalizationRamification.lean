/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Ramification after normalizing a local branch

These ring-level lemmas supply part of the normalization comparison in U1.
An essentially finite type local domain unramified over a local Dedekind domain
is itself Dedekind: unramifiedness identifies maximal ideals, so the source
maximal ideal is principal. Its normalization in its fraction field therefore
does not change the ring. In particular, every actual `Ideal.ramificationIdx`
of that normalization is one.

The base-change version starts with an arbitrary map `A → B`, a local
Dedekind `A`-algebra `R`, and a local domain quotient `C` of `R ⊗[A] B`.
Its normalization is specified by `IsIntegralClosure N C K`, where `K` is
the fraction field of `C`. A ramified prime of `N/R` then obstructs formal
unramifiedness of `A → B`.

The last version allows `C` to be a localization of the quotient and `N`
to be any local birational extension of `C`. Thus it applies to a chosen
local ring on the normalization without claiming that this localization
is itself integral over `C`.

The local proof combines [Stacks Tag 00UW](https://stacks.math.columbia.edu/tag/00UW)
(the maximal-ideal criterion for unramified maps) and
[Stacks Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
(the principal-maximal-ideal criterion for a DVR). The relevant Mathlib
declarations are `Algebra.FormallyUnramified.map_maximalIdeal`,
`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`, and
`Ideal.ramificationIdx_eq_one`. This is a different local proof from the
manuscript's étale-neighborhood argument for `prop:loci-compare`.

This file does not identify these rings with scheme stalks or identify an
abstract divisor dynamics with the actual normalized map. Those are separate
geometric inputs; a map between sets of divisors alone does not supply them.
-/

@[expose] public section

namespace Pcf

open IsLocalRing
open scoped TensorProduct

/-- An unramified local domain essentially of finite type over a local
Dedekind domain is Dedekind. Fields are allowed on either side. -/
theorem isDedekindDomain_of_formallyUnramified_local
    (R C : Type*) [CommRing R] [CommRing C]
    [IsDedekindDomain R] [IsLocalRing R] [IsDomain C] [IsLocalRing C]
    [Algebra R C] [IsLocalHom (algebraMap R C)]
    [Algebra.EssFiniteType R C] [Algebra.FormallyUnramified R C] :
    IsDedekindDomain C := by
  let : IsNoetherianRing C := Algebra.EssFiniteType.isNoetherianRing R C
  have hprincipal : (maximalIdeal C).IsPrincipal := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := C)]
    infer_instance
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain C).out 5 3).mp hprincipal

section Normalization

variable (R C N K : Type*)
    [CommRing R] [CommRing C] [CommRing N] [Field K]
    [IsDedekindDomain R] [IsLocalRing R] [IsDomain C] [IsLocalRing C]
    [Algebra R C] [IsLocalHom (algebraMap R C)] [Algebra.EssFiniteType R C]
    [Algebra C N] [Algebra R N] [IsScalarTower R C N]
    [Algebra C K] [IsFractionRing C K] [Algebra N K]
    [IsScalarTower C N K] [IsIntegralClosure N C K]

include K

/-- Normalizing an unramified local branch over a local Dedekind domain
preserves formal unramifiedness, because the branch is already normal. -/
theorem formallyUnramified_normalization_of_local
    [Algebra.FormallyUnramified R C] : Algebra.FormallyUnramified R N := by
  let : IsDedekindDomain C := isDedekindDomain_of_formallyUnramified_local R C
  exact Algebra.FormallyUnramified.of_equiv
    ((IsIntegralClosure.equiv C C K N).restrictScalars R)

/-- The genuine ramification index of a prime on the normalization of an
unramified local branch is one. No residue characteristic hypothesis is needed. -/
theorem ramificationIdx_normalization_eq_one_of_local
    [Algebra.FormallyUnramified R C] (q : Ideal N) [q.IsPrime] :
    q.ramificationIdx R = 1 := by
  let : IsDedekindDomain C := isDedekindDomain_of_formallyUnramified_local R C
  let e := (IsIntegralClosure.equiv C C K N).restrictScalars R
  let : Algebra.EssFiniteType R N :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  let : Algebra.FormallyUnramified R N :=
    formallyUnramified_normalization_of_local R C N K
  exact Ideal.ramificationIdx_eq_one q R

end Normalization

section BaseChange

variable (A B R C N K : Type*)
    [CommRing A] [CommRing B] [CommRing R] [CommRing C] [CommRing N] [Field K]
    [Algebra A B] [Algebra A R] [Algebra.EssFiniteType A B]
    [IsDedekindDomain R] [IsLocalRing R] [IsDomain C] [IsLocalRing C]
    [Algebra R C] [IsLocalHom (algebraMap R C)]
    [Algebra C N] [Algebra R N] [IsScalarTower R C N]
    [Algebra C K] [IsFractionRing C K] [Algebra N K]
    [IsScalarTower C N K] [IsIntegralClosure N C K]

include K

/-- Base change, passage to a local domain quotient, and normalization of that
branch cannot create a ramification index above one from an unramified map. -/
theorem ramificationIdx_normalization_eq_one_of_baseChange
    [Algebra.FormallyUnramified A B]
    (f : R ⊗[A] B →ₐ[R] C) (hf : Function.Surjective f)
    (q : Ideal N) [q.IsPrime] : q.ramificationIdx R = 1 := by
  let : Algebra.EssFiniteType R C := Algebra.EssFiniteType.of_surjective f hf
  let : Algebra.FormallyUnramified R C :=
    Algebra.FormallyUnramified.of_surjective f hf
  exact ramificationIdx_normalization_eq_one_of_local R C N K q

/-- A ramified prime of the actual normalization of a local base-change
branch detects failure of formal unramifiedness of the original ring map. -/
theorem not_formallyUnramified_of_one_lt_ramificationIdx_normalization
    (f : R ⊗[A] B →ₐ[R] C) (hf : Function.Surjective f)
    (q : Ideal N) [q.IsPrime] (hq : 1 < q.ramificationIdx R) :
    ¬ Algebra.FormallyUnramified A B := by
  intro h
  let : Algebra.FormallyUnramified A B := h
  have he := ramificationIdx_normalization_eq_one_of_baseChange A B R C N K f hf q
  exact (Nat.lt_irrefl 1) (he ▸ hq)

end BaseChange

section LocalizedBaseChange

variable (A B R D C N K : Type*)
    [CommRing A] [CommRing B] [CommRing R] [CommRing D]
    [CommRing C] [CommRing N] [Field K]
    [Algebra A B] [Algebra A R] [Algebra.EssFiniteType A B]
    [IsDedekindDomain R] [IsLocalRing R] [IsDomain C] [IsLocalRing C]
    [Algebra R D] [Algebra D C] [Algebra R C] [IsScalarTower R D C]
    [IsLocalHom (algebraMap R C)]
    [Algebra C N] [Algebra R N] [IsScalarTower R C N]
    [Algebra C K] [IsFractionRing C K] [Algebra N K]
    [IsScalarTower C N K] [IsIntegralClosure N C K]

include K

/-- The normalization comparison allows localization after taking the
base-change quotient. This includes local rings at primes of a branch. -/
theorem ramificationIdx_normalization_eq_one_of_localized_baseChange
    [Algebra.FormallyUnramified A B]
    (f : R ⊗[A] B →ₐ[R] D) (hf : Function.Surjective f)
    (M : Submonoid D) [IsLocalization M C]
    (q : Ideal N) [q.IsPrime] : q.ramificationIdx R = 1 := by
  let : Algebra.EssFiniteType R D := Algebra.EssFiniteType.of_surjective f hf
  let : Algebra.EssFiniteType D C := Algebra.EssFiniteType.of_isLocalization C M
  let : Algebra.EssFiniteType R C := Algebra.EssFiniteType.comp R D C
  let : Algebra.FormallyUnramified R D :=
    Algebra.FormallyUnramified.of_surjective f hf
  let : Algebra.FormallyUnramified D C :=
    Algebra.FormallyUnramified.of_isLocalization M
  let : Algebra.FormallyUnramified R C := Algebra.FormallyUnramified.comp R D C
  exact ramificationIdx_normalization_eq_one_of_local R C N K q

/-- Ramification on the normalization of a localized base-change branch
obstructs formal unramifiedness of the original map. -/
theorem not_formallyUnramified_of_one_lt_ramificationIdx_localized_normalization
    (f : R ⊗[A] B →ₐ[R] D) (hf : Function.Surjective f)
    (M : Submonoid D) [IsLocalization M C]
    (q : Ideal N) [q.IsPrime] (hq : 1 < q.ramificationIdx R) :
    ¬ Algebra.FormallyUnramified A B := by
  intro h
  let : Algebra.FormallyUnramified A B := h
  have he := ramificationIdx_normalization_eq_one_of_localized_baseChange
    A B R D C N K f hf M q
  exact (Nat.lt_irrefl 1) (he ▸ hq)

end LocalizedBaseChange

section BirationalLocalExtension

variable (C N K : Type*) [CommRing C] [CommRing N] [Field K]
    [IsDomain C] [ValuationRing C] [IsLocalRing N]
    [Algebra C N] [IsLocalHom (algebraMap C N)]
    [Algebra C K] [Algebra N K] [IsScalarTower C N K]
    [IsFractionRing C K] [IsFractionRing N K]

include K

/-- A local extension of a valuation ring inside its fraction field is an
isomorphism. This applies to a local ring of a normalization without assuming
that this localized ring is integral over the original local ring. -/
theorem bijective_algebraMap_of_local_birational :
    Function.Bijective (algebraMap C N) := by
  have h := bijective_rangeRestrict_comp_of_valuationRing
    (algebraMap C N) (algebraMap N K) (IsScalarTower.algebraMap_eq C N K).symm
  refine ⟨fun x y hxy ↦ h.1 (congrArg (algebraMap N K).rangeRestrict hxy), fun n ↦ ?_⟩
  obtain ⟨c, hc⟩ := h.2 ((algebraMap N K).rangeRestrict n)
  exact ⟨c, IsFractionRing.injective N K (congrArg Subtype.val hc)⟩

end BirationalLocalExtension

section LocalizedBirationalBaseChange

variable (A B R D C N K : Type*)
    [CommRing A] [CommRing B] [CommRing R] [CommRing D]
    [CommRing C] [CommRing N] [Field K]
    [Algebra A B] [Algebra A R] [Algebra.EssFiniteType A B]
    [IsDedekindDomain R] [IsLocalRing R] [IsDomain C] [IsLocalRing C]
    [Algebra R D] [Algebra D C] [Algebra R C] [IsScalarTower R D C]
    [IsLocalHom (algebraMap R C)] [IsLocalRing N]
    [Algebra C N] [IsLocalHom (algebraMap C N)]
    [Algebra R N] [IsScalarTower R C N]
    [Algebra C K] [IsFractionRing C K] [Algebra N K]
    [IsFractionRing N K] [IsScalarTower C N K]

include K

/-- The ramification comparison also holds for a birational local extension
of the branch, including a local ring of its normalization. -/
theorem ramificationIdx_eq_one_of_localized_birational_baseChange
    [Algebra.FormallyUnramified A B]
    (f : R ⊗[A] B →ₐ[R] D) (hf : Function.Surjective f)
    (M : Submonoid D) [IsLocalization M C]
    (q : Ideal N) [q.IsPrime] : q.ramificationIdx R = 1 := by
  let : Algebra.EssFiniteType R D := Algebra.EssFiniteType.of_surjective f hf
  let : Algebra.EssFiniteType D C := Algebra.EssFiniteType.of_isLocalization C M
  let : Algebra.EssFiniteType R C := Algebra.EssFiniteType.comp R D C
  let : Algebra.FormallyUnramified R D :=
    Algebra.FormallyUnramified.of_surjective f hf
  let : Algebra.FormallyUnramified D C :=
    Algebra.FormallyUnramified.of_isLocalization M
  let : Algebra.FormallyUnramified R C := Algebra.FormallyUnramified.comp R D C
  let : IsDedekindDomain C := isDedekindDomain_of_formallyUnramified_local R C
  have hCN := bijective_algebraMap_of_local_birational C N K
  let : Algebra.EssFiniteType R N :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom R C N) hCN.2
  let : Algebra.FormallyUnramified R N :=
    Algebra.FormallyUnramified.of_surjective (IsScalarTower.toAlgHom R C N) hCN.2
  exact Ideal.ramificationIdx_eq_one q R

/-- A genuine ramification index above one on a birational local extension
of a localized base-change branch detects ramification of the original map. -/
theorem not_formallyUnramified_of_one_lt_ramificationIdx_localized_birational
    (f : R ⊗[A] B →ₐ[R] D) (hf : Function.Surjective f)
    (M : Submonoid D) [IsLocalization M C]
    (q : Ideal N) [q.IsPrime] (hq : 1 < q.ramificationIdx R) :
    ¬ Algebra.FormallyUnramified A B := by
  intro h
  let : Algebra.FormallyUnramified A B := h
  have he := ramificationIdx_eq_one_of_localized_birational_baseChange
    A B R D C N K f hf M q
  exact (Nat.lt_irrefl 1) (he ▸ hq)

end LocalizedBirationalBaseChange

end Pcf
