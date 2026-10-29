/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SeparableNormalizedPCFIteration

/-!
# Recursive iteration invariance on actual point closures

The root separability and normalized non-étale PCF condition is now iterate
invariant. The remaining step reindexes every actual return morphism on the
original reduced point closure.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

private theorem pointClosureReturnMap_heq_of_eq
    {X : Scheme.{u}} {f g : X ⟶ X} (hfg : f = g)
    {x y : X} (hxy : x = y) (hx : f x = x) (hy : g y = y) :
    HEq (pointClosureReturnMap f x hx) (pointClosureReturnMap g y hy) := by
  cases hfg
  cases hxy
  rfl

/-- Reindex a return for an ambient power as the corresponding return for
the original morphism with both times multiplied by the exponent. -/
theorem eventuallyPeriodicPointReturn_ambient_pow_reindex
    {X : Scheme.{u}} (f : X ⟶ X) (m r p : ℕ) (x : X)
    (h : schemePointIterate (End.of f ^ m).asHom (r + p) x =
      schemePointIterate (End.of f ^ m).asHom r x) :
    HEq (eventuallyPeriodicPointReturn (End.of f ^ m).asHom r p x h)
      (eventuallyPeriodicPointReturn f (m * r) (m * p) x
        (schemePointIterate_periodic_of_pow f m r p x h)) := by
  unfold eventuallyPeriodicPointReturn
  apply pointClosureReturnMap_heq_of_eq
  · rw [show End.of (End.of f ^ m).asHom = End.of f ^ m from rfl,
      pow_mul]
  · exact schemePointIterate_pow f m r x

private theorem isPCFAllSubvarietiesAtDepth_of_heq_return
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (d : ℕ) {x y : X} (hxy : x = y)
    (v : (pointClosureIdealSheaf x).subscheme ⟶
      (pointClosureIdealSheaf x).subscheme)
    (w : (pointClosureIdealSheaf y).subscheme ⟶
      (pointClosureIdealSheaf y).subscheme)
    [IsFinite v] [IsDominant v] [IsFinite w] [IsDominant w]
    (hvw : HEq v w)
    (h : IsPCFAllSubvarietiesAtDepth k d
      ((pointClosureIdealSheaf x).subschemeι ≫ s) v) :
    IsPCFAllSubvarietiesAtDepth k d
      ((pointClosureIdealSheaf y).subschemeι ≫ s) w := by
  cases hxy
  cases hvw
  exact h

/-- Every recursive PCF chain for `f` is also a recursive PCF chain for
any positive ambient iterate. A return of `f^m` is exactly a return of
`f` with both times multiplied by `m`. -/
theorem isPCFAllSubvarietiesAtDepth_pow_of
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (m : ℕ) (hm : 1 ≤ m) (d : ℕ)
    (h : IsPCFAllSubvarietiesAtDepth k d s f) :
    IsPCFAllSubvarietiesAtDepth k d s (End.of f ^ m).asHom := by
  cases d with
  | zero =>
      exact (isSeparableNormalizedPCF_pow_iff k s f m hm).2 h
  | succ d =>
      refine ⟨(isSeparableNormalizedPCF_pow_iff k s f m hm).2 h.1, ?_⟩
      intro C r p hp hperiodic
      have hperiodicF :=
        schemePointIterate_periodic_of_pow f m r p C.1 hperiodic
      have hmp : 1 ≤ m * p := Nat.mul_pos hm hp
      have hretF := h.2 C (m * r) (m * p) hmp hperiodicF
      apply isPCFAllSubvarietiesAtDepth_of_heq_return k s d
        (schemePointIterate_pow f m r C.1).symm
        (eventuallyPeriodicPointReturn f (m * r) (m * p) C.1 hperiodicF)
        (eventuallyPeriodicPointReturn (End.of f ^ m).asHom r p C.1 hperiodic)
        (eventuallyPeriodicPointReturn_ambient_pow_reindex f m r p C.1 hperiodic).symm
      exact hretF

/-- The full recursive all-subvariety property passes from a map to each
positive iterate, on every original reduced return subvariety. -/
theorem isPCFAllSubvarieties_pow_of
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (m : ℕ) (hm : 1 ≤ m)
    (h : IsPCFAllSubvarieties k s f) :
    IsPCFAllSubvarieties k s (End.of f ^ m).asHom := by
  intro d
  exact isPCFAllSubvarietiesAtDepth_pow_of k s f m hm d (h d)

#print axioms eventuallyPeriodicPointReturn_ambient_pow_reindex
#print axioms isPCFAllSubvarietiesAtDepth_of_heq_return
#print axioms isPCFAllSubvarietiesAtDepth_pow_of
#print axioms isPCFAllSubvarieties_pow_of

end Pcf
