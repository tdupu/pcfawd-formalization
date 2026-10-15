/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Pcf.Stacks.Abhyankar.StandardCover

/-!
# The regular reduced divisor in the standard Abhyankar cover

The addendum in Stacks Tag `0EYH` identifies the reduced inverse image of the regular divisor in
the standard model `R[z]/(z^e-u*a)` with the original divisor.  The underlying quotient
equivalence is `Pcf.LocalModel.quotientRootEquiv`.  This file records its exact regularity
consequence and packages it with the already proved finite-free and Cartier-divisor clauses.

This is the local-model verification in `0EYH`; it does not assert that an arbitrary
normalization is locally of this form, which is the remaining descent/normalization assembly.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

open Polynomial

variable {R : Type u} [CommRing R]

/-- In a standard tame cover, the reduced divisor cut out by the root is regular whenever the
original divisor is regular.  This is clause (3) of Stacks Tag `0EYH` after the standard local
presentation has been obtained. -/
theorem standardCover_rootQuotient_isRegularRing
    (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] :
    IsRegularRing
      (AdjoinRoot (Pcf.LocalModel.localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (Pcf.LocalModel.localPoly u a e)} :
          Set (AdjoinRoot (Pcf.LocalModel.localPoly u a e)))) :=
  IsRegularRing.of_ringEquiv
    (Pcf.LocalModel.quotientRootEquiv u a he).symm.toRingEquiv

/-- The standard model has the three local structural properties used in Tag `0EYH`: it is
finite and free over the base, its reduced divisor equation is a nonzerodivisor, and the
corresponding reduced divisor is regular. -/
theorem standardCover_finite_free_cartier_regular
    (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e) (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] :
    Module.Finite R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) ∧
      Module.Free R (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) ∧
      AdjoinRoot.root (Pcf.LocalModel.localPoly u a e) ∈
        nonZeroDivisors (AdjoinRoot (Pcf.LocalModel.localPoly u a e)) ∧
      IsRegularRing
        (AdjoinRoot (Pcf.LocalModel.localPoly u a e) ⧸
          Ideal.span ({AdjoinRoot.root (Pcf.LocalModel.localPoly u a e)} :
            Set (AdjoinRoot (Pcf.LocalModel.localPoly u a e)))) := by
  exact ⟨standardCover_finite u a he, standardCover_free u a he,
    Pcf.LocalModel.root_mem_nonZeroDivisors u a he ha,
    standardCover_rootQuotient_isRegularRing u a he⟩

end Pcf.Stacks
