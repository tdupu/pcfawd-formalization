/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Pcf.Stacks.Purity.PuncturedSpectrum

/-!
# Unconditional punctured-spectrum predecessors for Tag 0BM9

This file separates the elementary topological and injectivity halves of the Hartogs argument in
Stacks Tag `0BM9` from its missing surjectivity half.  For a Noetherian local ring the punctured
spectrum is quasi-compact.  For a local domain of positive dimension, it is nonempty and
restriction of regular functions from the whole spectrum to the puncture is injective.

The corresponding surjectivity statement for a normal Noetherian local domain of dimension at
least two is not asserted: it is precisely the depth-two/reflexive Hartogs theorem absent from the
pinned Mathlib revision.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

universe u

namespace Pcf.Stacks

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The punctured spectrum of a Noetherian local ring is quasi-compact. -/
theorem isCompact_puncturedSpectrum [IsNoetherianRing R] :
    IsCompact (puncturedSpectrum R).1 :=
  NoetherianSpace.isCompact _

/-- A Noetherian local punctured spectrum admits a finite cover by basic opens whose defining
elements generate the maximal ideal.  This is the affine cover on which the depth-two Hartogs
calculation is performed. -/
theorem exists_finite_basicOpen_cover_puncturedSpectrum [IsNoetherianRing R] :
    ∃ s : Set R, s.Finite ∧ Ideal.span s = IsLocalRing.maximalIdeal R ∧
      puncturedSpectrum R = ⨆ x : s, PrimeSpectrum.basicOpen x.1 := by
  obtain ⟨s, hs, hspan⟩ :=
    Submodule.fg_def.mp (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  refine ⟨s, hs, hspan, ?_⟩
  change (show TopologicalSpace.Opens (PrimeSpectrum R) from puncturedSpectrum R) =
    ⨆ x : s, PrimeSpectrum.basicOpen x.1
  apply SetLike.ext'
  rw [TopologicalSpace.Opens.coe_iSup]
  ext p
  simp only [Set.mem_iUnion, SetLike.mem_coe, puncturedSpectrum,
    PrimeSpectrum.mem_basicOpen]
  constructor
  · intro hp
    by_contra h
    push Not at h
    have hs_le : s ⊆ p.asIdeal := fun x hx ↦ h ⟨x, hx⟩
    have hm_le : IsLocalRing.maximalIdeal R ≤ p.asIdeal := by
      rw [← hspan]
      exact Ideal.span_le.mpr hs_le
    have hp_le : p.asIdeal ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal p.isPrime.ne_top
    apply hp
    apply PrimeSpectrum.ext
    change p.asIdeal = IsLocalRing.maximalIdeal R
    exact le_antisymm hp_le hm_le
  · rintro ⟨x, hx⟩ hp
    have hxm : x.1 ∈ IsLocalRing.maximalIdeal R := by
      rw [← hspan]
      exact Ideal.subset_span x.2
    apply hx
    rw [hp]
    exact hxm

/-- The maximal ideal of a positive-dimensional local domain is nonzero. -/
theorem maximalIdeal_ne_bot_of_one_le_ringKrullDim [IsDomain R]
    (hdim : 1 ≤ ringKrullDim R) : IsLocalRing.maximalIdeal R ≠ ⊥ := by
  intro hm
  have hheight : (IsLocalRing.maximalIdeal R).height = 0 :=
    Ideal.height_eq_zero_iff_eq_bot.mpr hm
  have hdim0 : ringKrullDim R = 0 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    simp [hheight]
  have hzero : ¬(1 ≤ ringKrullDim R) := by
    rw [hdim0]
    exact not_le_of_gt zero_lt_one
  exact hzero hdim

/-- A local domain of positive Krull dimension has a nonempty punctured spectrum. -/
theorem puncturedSpectrum_nonempty_of_one_le_ringKrullDim [IsDomain R]
    (hdim : 1 ≤ ringKrullDim R) : Nonempty (puncturedSpectrum R) := by
  have hm := maximalIdeal_ne_bot_of_one_le_ringKrullDim R hdim
  change Nonempty {x : PrimeSpectrum R // x ≠ IsLocalRing.closedPoint R}
  refine ⟨⟨⊥, ?_⟩⟩
  intro h
  apply hm
  exact (congrArg PrimeSpectrum.asIdeal h).symm

/-- Restriction of regular functions from an integral affine scheme to its nonempty punctured
spectrum is injective.  Thus the remaining ring-level Hartogs obstruction in Tag `0BM9` is
surjectivity, not uniqueness of extension. -/
theorem puncturedSpectrum_restriction_injective [IsDomain R]
    (hdim : 1 ≤ ringKrullDim R) :
    Function.Injective
      ((Spec (.of R)).presheaf.map
        (homOfLE le_top : puncturedSpectrum R ⟶ ⊤).op) := by
  let _ : Nonempty (puncturedSpectrum R) :=
    puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hdim
  exact map_injective_of_isIntegral (Spec (.of R))
    (homOfLE le_top : puncturedSpectrum R ⟶ ⊤)

end Pcf.Stacks
