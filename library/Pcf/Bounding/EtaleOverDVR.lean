/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Étale extensions of a discrete valuation ring

A local ring that is essentially of finite type and formally étale over a
discrete valuation ring, with the maximal ideal lying over the maximal ideal,
is again a discrete valuation ring, provided it is a domain that is not a
field. Its ramification index is one. In `latex/paper-p.tex`, proof of
Theorem `thm:allcodim-normal`, this is applied to the restriction of the
normalized blow-up map to an exceptional component at a point where the tame
bounding chart makes it étale.
-/

@[expose] public section

namespace Pcf

open IsLocalRing

universe u v

/-- A formally unramified local extension of a discrete valuation ring that
is a noetherian domain but not a field is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_formallyUnramified
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDiscreteValuationRing R]
    [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (hS : ¬IsField S) : IsDiscreteValuationRing S := by
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hprin : (maximalIdeal S).IsPrincipal := by
    refine ⟨⟨algebraMap R S ϖ, ?_⟩⟩
    rw [← hmax, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  exact ((IsDiscreteValuationRing.TFAE S hS).out 1 5).mpr hprin

#print axioms isDiscreteValuationRing_of_formallyUnramified

end Pcf
