/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyRecursive

/-!
# Geometric iteration identities for all-subvariety returns

The proof of `latex/paper-p.tex`, Lemma `lem:allsubvar-iterate`, uses the
identity that the return of an ambient iterate on a periodic reduced point
closure is the corresponding iterate of its actual return morphism. These
lemmas establish that identity on the original, possibly nonnormal closure.

The full recursive PCF equivalence additionally needs iteration invariance
for the normalized non-etale branch predicate and separability at every
recursive node.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Pcf

noncomputable section

/-- A return datum at time `s` gives returns at every multiple `s*m`,
on the same original reduced point closure. -/
theorem schemePointIterate_periodic_mul
    {X : Scheme.{u}} (f : X ⟶ X) (r s m : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    schemePointIterate f (r + s * m) x = schemePointIterate f r x := by
  have hfixed := schemePointIterate_periodic f r s x h
  have hm := end_pow_apply_eq_of_apply_eq (End.of f ^ s).asHom
    (schemePointIterate f r x) hfixed m
  unfold schemePointIterate at hm ⊢
  rw [Nat.add_comm r (s * m), pow_add]
  change ((End.of f ^ (s * m)).asHom.base
    ((End.of f ^ r).asHom.base x)) = (End.of f ^ r).asHom.base x
  rw [pow_mul]
  exact hm

/-- The `m`-fold iterate of an eventual return map is exactly the return
of the `s*m`-th ambient iterate on the same original reduced closure. -/
theorem eventuallyPeriodicPointReturn_pow
    {X : Scheme.{u}} (f : X ⟶ X) (r s m : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    (End.of (eventuallyPeriodicPointReturn f r s x h) ^ m).asHom =
      eventuallyPeriodicPointReturn f r (s * m) x
        (schemePointIterate_periodic_mul f r s m x h) := by
  unfold eventuallyPeriodicPointReturn
  rw [pointClosureReturnMap_iterate]
  simp only [pow_mul]

/-- If `B = f^r(C)` has return time `s` under `f`, then `B` is periodic
with return time `s` under every ambient iterate `f^m`. This is the
geometric reindexing in the converse direction of
`paper-p.tex`, Lemma `lem:allsubvar-iterate`. -/
theorem schemePointIterate_periodic_for_ambient_pow
    {X : Scheme.{u}} (f : X ⟶ X) (r s m : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    schemePointIterate (End.of f ^ m).asHom s
      (schemePointIterate f r x) = schemePointIterate f r x := by
  have hfixed := schemePointIterate_periodic f r s x h
  have hm := end_pow_apply_eq_of_apply_eq (End.of f ^ s).asHom
    (schemePointIterate f r x) hfixed m
  unfold schemePointIterate at hm ⊢
  change ((End.of f ^ m) ^ s).asHom.base ((End.of f ^ r).asHom.base x) =
    (End.of f ^ r).asHom.base x
  rw [← pow_mul, Nat.mul_comm m s, pow_mul]
  exact hm

/-- The return morphism induced by `f^m` on the original reduced closure
`B=f^r(C)` agrees with the `m`-th power of the return morphism induced by
`f`. The periodicity proof for `f^m` is supplied by the preceding theorem. -/
theorem eventuallyPeriodicPointReturn_ambient_pow_eq
    {X : Scheme.{u}} (f : X ⟶ X) (r s m : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x)
    (hB : schemePointIterate (End.of f ^ m).asHom (0 + s)
      (schemePointIterate f r x) =
      schemePointIterate (End.of f ^ m).asHom 0
        (schemePointIterate f r x)) :
    (End.of (eventuallyPeriodicPointReturn f r s x h) ^ m).asHom =
      eventuallyPeriodicPointReturn (End.of f ^ m).asHom 0 s
        (schemePointIterate f r x) hB := by
  rw [eventuallyPeriodicPointReturn_pow]
  unfold eventuallyPeriodicPointReturn
  simp only [schemePointIterate]
  congr 1
  change (End.of f ^ (s * m)).asHom = ((End.of f ^ m) ^ s).asHom
  rw [Nat.mul_comm s m, pow_mul]

/-- The geometric identity needed in the converse implication of iteration
invariance, with the return datum under `f^m` constructed from the original
return datum rather than assumed. -/
theorem eventuallyPeriodicPointReturn_pow_on_image
    {X : Scheme.{u}} (f : X ⟶ X) (r s m : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    (End.of (eventuallyPeriodicPointReturn f r s x h) ^ m).asHom =
      eventuallyPeriodicPointReturn (End.of f ^ m).asHom 0 s
        (schemePointIterate f r x)
        (by simpa [schemePointIterate] using
          schemePointIterate_periodic_for_ambient_pow f r s m x h) := by
  exact eventuallyPeriodicPointReturn_ambient_pow_eq f r s m x h _

end

end Pcf
