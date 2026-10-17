/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Basic opens of an affine open and prime ideals

`Pcf.Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf`: for `x` in an affine open `V`
and `f ∈ Γ(X, V)`, `x ∈ D(f)` iff `f ∉ 𝔭_x`, where `𝔭_x = hV.primeIdealOf x`.  This is the single
proof of this fact in pcf; the purity, bounding and Abhyankar layers call it.  (A candidate for
Mathlib as `IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf`.)
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace Pcf.Stacks.SchemeLevel

/-- `x ∈ D(f)` iff `f ∉ 𝔭_x`, for `x` in an affine open. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (f : Γ(X, V)) (x : V) :
    (x : X) ∈ X.basicOpen f ↔ f ∉ (hV.primeIdealOf x).asIdeal := by
  rw [← hV.fromSpec_primeIdealOf x]
  change hV.primeIdealOf x ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
  rw [hV.fromSpec_preimage_basicOpen]
  rfl

end Pcf.Stacks.SchemeLevel
