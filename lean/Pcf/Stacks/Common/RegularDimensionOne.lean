/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Pcf.Bounding.RegularLocalDomain

/-!
# One-dimensional regular local rings

This file records the direction of Stacks Project Tag `00PD` used in the
dimension-one case of purity: a regular local ring of Krull dimension one is a
discrete valuation ring.

The full tag is an equivalence of five conditions.  The declaration below is
therefore tagged only as the `(3) => (1)` direction, rather than as the whole
tag.  Its domain input is supplied by the already formalized Tag `00NP`.
-/

namespace Pcf.Stacks

open IsLocalRing

local instance regularLocal_isDomain
    (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_isRegularLocalRing R

/-- **Stacks Project Tag 00PD, `(3) => (1)`.** A one-dimensional regular
local ring is a discrete valuation ring. -/
@[stacks 00PD "(3) => (1)"]
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  rw [hdim] at hreg
  exact_mod_cast hreg

#print axioms isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one

end Pcf.Stacks
