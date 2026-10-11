/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The numerical DVR cancellation in Abhyankar's lemma

Stacks Project Tag `0BRM` concludes formal smoothness in the adic topology after a
ramified base change.  Its last step compares two towers of DVRs and cancels equal positive
ramification indices.  This file proves that cancellation for Mathlib's actual
`Ideal.ramificationIdx`, and derives the corresponding local unramifiedness criterion when
the residue-field extension is separable.

This is not the full tag: pinned Mathlib has algebraic `Algebra.FormallySmooth` and adic
topologies, but no predicate expressing formal smoothness *in the adic topology*.  The
declarations here therefore carry no `0BRM` tag.
-/

universe u v w

namespace Pcf.Stacks

/-- In a flat tower, if the ramification index at the top is unchanged from the index at
the intermediate prime, the top extension has ramification index one.

This is the numerical cancellation at the end of the proof of Stacks Tag `0BRM`. -/
theorem ramificationIdx_over_intermediate_eq_one_of_total_eq
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite R S] [Module.Flat S T]
    (r : Ideal T) [r.IsPrime]
    (h : r.ramificationIdx R = (r.under S).ramificationIdx R) :
    r.ramificationIdx S = 1 := by
  have hpos : 0 < (r.under S).ramificationIdx R :=
    Ideal.ramificationIdx_pos (r.under S) R
  have htower := Ideal.ramificationIdx_tower (R := R) (S := S) (T := T) (r.under S) r
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← htower, h, mul_one]

/-- Under separability of the residue-field extension, the numerical cancellation gives
unramifiedness at the actual top prime.  This is the algebraic local conclusion used inside
Tag `0BRM`, before its stronger adic formal-smoothness conclusion. -/
theorem isUnramifiedAt_of_ramificationIdx_total_eq_intermediate
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite R S] [Module.Flat S T] [Algebra.EssFiniteType S T]
    (r : Ideal T) [r.IsPrime]
    [Algebra.HasSeparableResidueFieldsAt S T (r.under S)]
    (h : r.ramificationIdx R = (r.under S).ramificationIdx R) :
    Algebra.IsUnramifiedAt S r := by
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact ramificationIdx_over_intermediate_eq_one_of_total_eq R S T r h

#print axioms ramificationIdx_over_intermediate_eq_one_of_total_eq
#print axioms isUnramifiedAt_of_ramificationIdx_total_eq_intermediate

end Pcf.Stacks
