/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharP
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod

/-!
# The wild example's orbit in the actual ground field

The existing symbolic degree argument is specialized at an actual element
transcendental over the prime field. Thus the orbit is infinite in `k`, not
only in a formal polynomial ring.
-/

@[expose] public section
namespace Pcf.Examples.PaperP.Wild
open Polynomial
variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

local instance primeFieldAlgebra : Algebra (ZMod p) k := ZMod.algebra k p

/-- The polynomial return on the invariant line in the finite chart. -/
noncomputable def returnPolynomial (c : k) : k[X] := X ^ (p + 1) + C c

/-- The corresponding function on the ground field. -/
def returnFunction (c t : k) : k := t ^ (p + 1) + c

omit [Fact p.Prime] in
/-- The polynomial derivative in the source example. -/
theorem returnPolynomial_derivative (c : k) :
    (returnPolynomial k p c).derivative = X ^ p := by
  simp [returnPolynomial, CharP.cast_eq_zero]

/-- Evaluation of the existing symbolic orbit gives the actual function orbit. -/
theorem orbit_aeval_eq_iterate (c : k) (n : ℕ) :
    Polynomial.aeval c (Pcf.Examples.CharP.orbit (ZMod p) p n) =
      (returnFunction k p c)^[n] 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Pcf.Examples.CharP.orbit_succ, map_add, map_pow, Polynomial.aeval_X, ih]
    simpa only [returnFunction] using
      (Function.iterate_succ_apply' (returnFunction k p c) n (0 : k)).symm

/-- The derivative has exactly one zero in the finite ground-field chart. -/
theorem returnPolynomial_derivative_eval_zero_iff (c t : k) :
    (returnPolynomial k p c).derivative.eval t = 0 ↔ t = 0 := by
  rw [returnPolynomial_derivative]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  exact pow_eq_zero_iff (Nat.ne_of_gt (Fact.out : p.Prime).pos)

/-- The actual critical-point orbit is injective over a transcendental parameter. -/
theorem returnFunction_orbit_injective (c : k) (hc : Transcendental (ZMod p) c) :
    Function.Injective (fun n : ℕ => (returnFunction k p c)^[n] 0) := by
  have he := (transcendental_iff_injective.mp hc).comp
    (Pcf.Examples.CharP.orbit_injective (K := ZMod p) (d := p) (Fact.out : p.Prime).one_lt.le)
  simpa only [Function.comp_def, orbit_aeval_eq_iterate] using he

/-- The critical point has infinite forward orbit in the actual field. -/
theorem returnFunction_orbit_infinite (c : k) (hc : Transcendental (ZMod p) c) :
    (Set.range (fun n : ℕ => (returnFunction k p c)^[n] 0)).Infinite :=
  Set.infinite_range_of_injective (returnFunction_orbit_injective k p c hc)

/-- The critical value `c` also has infinite forward orbit. -/
theorem returnFunction_criticalValue_orbit_infinite (c : k)
    (hc : Transcendental (ZMod p) c) :
    (Set.range (fun n : ℕ => (returnFunction k p c)^[n] c)).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  have hm : (returnFunction k p c)^[m] c = (returnFunction k p c)^[m + 1] 0 := by
    rw [Function.iterate_succ_apply]
    simp [returnFunction]
  have hn : (returnFunction k p c)^[n] c = (returnFunction k p c)^[n + 1] 0 := by
    rw [Function.iterate_succ_apply]
    simp [returnFunction]
  change (returnFunction k p c)^[m] c = (returnFunction k p c)^[n] c at h
  rw [hm, hn] at h
  exact Nat.add_right_cancel (returnFunction_orbit_injective k p c hc h)

#print axioms returnPolynomial_derivative
#print axioms returnPolynomial_derivative_eval_zero_iff
#print axioms orbit_aeval_eq_iterate
#print axioms returnFunction_orbit_injective
#print axioms returnFunction_orbit_infinite
#print axioms returnFunction_criticalValue_orbit_infinite
end Pcf.Examples.PaperP.Wild
