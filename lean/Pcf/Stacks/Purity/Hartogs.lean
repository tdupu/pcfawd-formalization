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

/-- A local domain of positive Krull dimension has a nonempty punctured spectrum. -/
theorem puncturedSpectrum_nonempty_of_one_le_ringKrullDim [IsDomain R]
    (hdim : 1 ≤ ringKrullDim R) : Nonempty (puncturedSpectrum R) := by
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := by
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
