/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Ring

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

@[expose] public section

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
    Ideal.ramificationIdx_pos (R := R) (r.under S)
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

set_option linter.style.haveILetI false in
/-- An explicit-prime form of the local ramification-index criterion.

This avoids forcing downstream arguments to transport the dependent
`HasSeparableResidueFieldsAt` class across an equality `r.under S = p`: the chosen prime
`p` and the lying-over witness are part of the statement. -/
theorem isUnramifiedAt_of_ramificationIdx_total_eq_intermediate_at
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite R S] [Module.Flat S T] [Algebra.EssFiniteType S T]
    (p : Ideal S) [p.IsPrime]
    (r : Ideal T) [r.IsPrime] [r.LiesOver p]
    [Algebra.HasSeparableResidueFieldsAt S T p]
    (h : r.ramificationIdx R = p.ramificationIdx R) :
    Algebra.IsUnramifiedAt S r := by
  have hram : r.ramificationIdx S = 1 :=
    ramificationIdx_over_intermediate_eq_one_of_total_eq R S T r <| by
      simpa only [← r.over_def p] using h
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at hram
  let Sp := Localization.AtPrime p
  let Tr := Localization.AtPrime r
  letI : Algebra Sp Tr := Localization.AtPrime.algebraOfLiesOver p r
  haveI : Algebra.EssFiniteType Sp Tr := Algebra.EssFiniteType.of_comp S Sp Tr
  suffices Algebra.FormallyUnramified Sp Tr from
    Algebra.FormallyUnramified.comp S Sp Tr
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
  exact ⟨Algebra.HasSeparableResidueFieldsAt.isSeparable r, by
    simpa only [← r.over_def p] using hram⟩

#print axioms ramificationIdx_over_intermediate_eq_one_of_total_eq
#print axioms isUnramifiedAt_of_ramificationIdx_total_eq_intermediate
#print axioms isUnramifiedAt_of_ramificationIdx_total_eq_intermediate_at

end Pcf.Stacks
