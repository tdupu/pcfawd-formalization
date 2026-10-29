/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The Stacks notion of a normal ring

Stacks Definition 10.37.11 (Tag `00GV`, in Section `037B`) defines a normal ring by requiring
every localization at a prime ideal to be a normal domain.  This differs from Mathlib's
`IsIntegrallyClosed` for rings with zero divisors.
The distinction matters in Tag `0BM9`, where the finite normal algebra need not be connected.

This file records the literal local definition.  It also proves compatibility with Mathlib's
domain-level notion, closure under finite products, and the elementary consequence that a
Stacks-normal ring is reduced.  No converse decomposition into a finite product of normal domains
is asserted here; that requires the Noetherian minimal-prime/idempotent decomposition API which is
not available at the pinned revision in the form needed by the proof of Tag `0BM9`.
-/

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false

namespace Pcf.Stacks

/-- A commutative ring is normal in the sense of Stacks Tag `00GV` (Definition 10.37.11) if its
localization at every prime ideal is a normal domain.  Unlike Mathlib's `IsIntegrallyClosed`,
this definition faithfully allows disconnected rings. -/
@[stacks 00GV]
def IsStacksNormalRing (R : Type*) [CommRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

namespace IsStacksNormalRing

variable {R : Type*} [CommRing R]

/-- Every local ring at a prime of a Stacks-normal ring is a domain. -/
theorem isDomain_atPrime (hR : IsStacksNormalRing R) (p : PrimeSpectrum R) :
    IsDomain (Localization.AtPrime p.asIdeal) :=
  (hR p).1

/-- Every local ring at a prime of a Stacks-normal ring is integrally closed. -/
theorem isIntegrallyClosed_atPrime (hR : IsStacksNormalRing R) (p : PrimeSpectrum R) :
    IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
  (hR p).2

/-- A normal domain in Mathlib's sense is a normal ring in the Stacks sense. -/
theorem of_isDomain [IsDomain R] [IsIntegrallyClosed R] : IsStacksNormalRing R := by
  intro p
  constructor
  · infer_instance
  · exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

/-- On domains, the Stacks definition agrees with Mathlib's `IsIntegrallyClosed`. -/
theorem iff_isIntegrallyClosed [IsDomain R] :
    IsStacksNormalRing R ↔ IsIntegrallyClosed R := by
  constructor
  · intro hR
    apply IsIntegrallyClosed.of_localization_maximal
    intro p _ hp
    exact (hR ⟨p, hp.isPrime⟩).2
  · intro _
    exact of_isDomain

/-- A Stacks-normal ring is reduced. -/
theorem isReduced (hR : IsStacksNormalRing R) : IsReduced R := by
  apply isReduced_ofLocalizationMaximal R
  intro p hp
  let _ : p.IsPrime := hp.isPrime
  let _ : IsDomain (Localization.AtPrime p) := (hR ⟨p, inferInstance⟩).1
  infer_instance

/-- Stacks-normality is invariant under ring isomorphism. -/
theorem of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hB : IsStacksNormalRing B) : IsStacksNormalRing A := by
  intro p
  let q : PrimeSpectrum B := ⟨p.asIdeal.comap e.symm.toRingHom, inferInstance⟩
  have hpq : p.asIdeal = q.asIdeal.comap e.toRingHom := by
    dsimp [q]
    rw [Ideal.comap_comap, ← RingEquiv.toRingHom_eq_coe]
    simp
  let t : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    Localization.localRingEquiv p.asIdeal q.asIdeal e hpq
  let _ : IsDomain (Localization.AtPrime q.asIdeal) := (hB q).1
  let _ : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) := (hB q).2
  exact ⟨t.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv t.symm⟩

/-- A finite product of Stacks-normal rings is Stacks-normal.  This is the elementary
disconnected closure property needed for the componentwise reduction in Tag `0BM9`. -/
theorem pi {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)] [Finite ι]
    (hA : ∀ i, IsStacksNormalRing (A i)) :
    IsStacksNormalRing (∀ i, A i) := by
  intro p
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  rw [← hq]
  let e : Localization.AtPrime
        (q.asIdeal.comap (Pi.evalRingHom A i)) ≃+* Localization.AtPrime q.asIdeal :=
    RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
      (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
  let _ : IsDomain (Localization.AtPrime q.asIdeal) := (hA i q).1
  let _ : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) := (hA i q).2
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end IsStacksNormalRing

/-- Integral closures along a base-ring isomorphism have the same underlying elements of the
ambient algebra. -/
noncomputable def integralClosureRingEquivOfBaseRingEquiv
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R T] [Algebra S T]
    (φ : R ≃+* S)
    (hcomp : (algebraMap S T).comp φ.toRingHom = algebraMap R T) :
    integralClosure S T ≃+* integralClosure R T := {
    toFun := fun x => ⟨x.1, (φ.isIntegral_iff hcomp x.1).mpr x.2⟩
    invFun := fun x => ⟨x.1, (φ.isIntegral_iff hcomp x.1).mp x.2⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl
    map_mul' := by intro x y; apply Subtype.ext; rfl
    map_add' := by intro x y; apply Subtype.ext; rfl }

/-- Normality of an integral closure is unchanged when its base ring is reidentified by a ring
isomorphism. -/
theorem integralClosure_isStacksNormalRing_of_baseRingEquiv
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R T] [Algebra S T]
    (φ : R ≃+* S)
    (hcomp : (algebraMap S T).comp φ.toRingHom = algebraMap R T) :
    IsStacksNormalRing (integralClosure R T) →
      IsStacksNormalRing (integralClosure S T) := by
  intro h
  exact IsStacksNormalRing.of_ringEquiv
    (integralClosureRingEquivOfBaseRingEquiv R S T φ hcomp) h

end Pcf.Stacks
