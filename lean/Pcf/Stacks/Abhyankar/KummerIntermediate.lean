/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.LocalModel

/-!
# The root algebra occurring in Stacks Tag 09EV

Tag `09EV` starts from a DVR `A`, a uniformizer `π`, and the root extension
`K(π^(1/n))`.  Its proof first studies `A[x]/(x^n-π)`.  This file records the
independently useful, already unconditional algebraic part of that construction: the root
algebra is finite free of rank `n`, its root has the expected equation and is a
nonzerodivisor, and quotienting by the root gives `A/(π)`.

This is not the full tag.  In particular it does not claim that the root algebra is a DVR
or the integral closure, nor does it classify intermediate fields.  Those are clauses
(2)--(6) of `09EV`, and no declaration here carries that Stacks tag.
-/

universe u

open Polynomial

namespace Pcf.Stacks

variable {A : Type u} [CommRing A]

/-- The polynomial `X^n-π` used in Stacks Tag `09EV`. -/
noncomputable def dvrRootPoly (π : A) (n : ℕ) : A[X] := X ^ n - C π

/-- The `09EV` root polynomial is the standard local model with unit `1`. -/
theorem dvrRootPoly_eq_localPoly (π : A) (n : ℕ) :
    dvrRootPoly π n = Pcf.LocalModel.localPoly (1 : Aˣ) π n := by
  simp [dvrRootPoly, Pcf.LocalModel.localPoly]

/-- `X^n-π` is monic for positive `n`. -/
theorem dvrRootPoly_monic (π : A) {n : ℕ} (hn : 1 ≤ n) : (dvrRootPoly π n).Monic := by
  rw [dvrRootPoly_eq_localPoly]
  exact Pcf.LocalModel.localPoly_monic 1 π hn

/-- The root algebra in `09EV` is finite free over `A`. -/
theorem dvrRootAlgebra_finite (π : A) {n : ℕ} (hn : 1 ≤ n) :
    Module.Finite A (AdjoinRoot (dvrRootPoly π n)) := by
  rw [dvrRootPoly_eq_localPoly]
  exact Pcf.LocalModel.finite 1 π hn

/-- The root algebra in `09EV` is free over `A`. -/
theorem dvrRootAlgebra_free (π : A) {n : ℕ} (hn : 1 ≤ n) :
    Module.Free A (AdjoinRoot (dvrRootPoly π n)) := by
  rw [dvrRootPoly_eq_localPoly]
  exact Pcf.LocalModel.free 1 π hn

/-- The root algebra has rank `n`, the module-theoretic input to clause (1) of `09EV`. -/
theorem dvrRootAlgebra_finrank [Nontrivial A] (π : A) {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank A (AdjoinRoot (dvrRootPoly π n)) = n := by
  rw [dvrRootPoly_eq_localPoly]
  exact Pcf.LocalModel.finrank_eq 1 π hn

/-- The distinguished root satisfies `root^n = π`. -/
theorem dvrRoot_pow_eq (π : A) (n : ℕ) :
    AdjoinRoot.root (dvrRootPoly π n) ^ n =
      algebraMap A (AdjoinRoot (dvrRootPoly π n)) π := by
  rw [dvrRootPoly_eq_localPoly]
  simpa using Pcf.LocalModel.root_pow_eq (1 : Aˣ) π n

/-- Quotienting the root algebra by its distinguished root gives `A/(π)`.  This is the
residue-ring calculation used to prove locality and the DVR assertion in `09EV`. -/
noncomputable def dvrRootQuotientEquiv (π : A) {n : ℕ} (hn : 1 ≤ n) :
    (AdjoinRoot (dvrRootPoly π n) ⧸
      Ideal.span ({AdjoinRoot.root (dvrRootPoly π n)} :
        Set (AdjoinRoot (dvrRootPoly π n)))) ≃ₐ[A]
      A ⧸ Ideal.span ({π} : Set A) := by
  rw [dvrRootPoly_eq_localPoly]
  exact Pcf.LocalModel.quotientRootEquiv 1 π hn

/-- When `π` is a nonzerodivisor, so is the distinguished root. -/
theorem dvrRoot_mem_nonZeroDivisors (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : π ∈ nonZeroDivisors A) :
    AdjoinRoot.root (dvrRootPoly π n) ∈ nonZeroDivisors (AdjoinRoot (dvrRootPoly π n)) := by
  rw [dvrRootPoly_eq_localPoly]
  exact Pcf.LocalModel.root_mem_nonZeroDivisors 1 π hn hπ

#print axioms dvrRootAlgebra_finrank
#print axioms dvrRootAlgebra_free
#print axioms dvrRootQuotientEquiv
#print axioms dvrRoot_mem_nonZeroDivisors

end Pcf.Stacks
