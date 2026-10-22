/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PeriodicLift
public import Pcf.Bounding.AllSubvarietyGeometry

/-!
# Periodic lifts over a finite scheme cover in every codimension

A finite dominant map between integral schemes has nonempty finite point
fibres. A commuting self-map permutes the points in a fibre over a periodic
point after the downstairs return; finite dynamics supplies a periodic lift.
These points are generic points of the original integral reduced closures,
so there is no divisor or normality restriction.
-/

@[expose] public section

namespace Pcf

open CategoryTheory AlgebraicGeometry

universe u

/-- Iteration of the underlying point map agrees with the scheme morphism
power. -/
theorem schemePointIterate_eq_function_iterate
    {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) (x : X) :
    schemePointIterate f n x = (fun y : X => f y)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      unfold schemePointIterate at ih ⊢
      rw [pow_succ, End.mul_asHom]
      change (End.of f ^ n).asHom.base (f x) = (fun y : X => f y)^[n + 1] x
      rw [Function.iterate_succ_apply]
      exact ih (f x)

/-- A periodic point of a finite dominant integral scheme cover has a
periodic point above it for a commuting upstairs map. This works for generic
points of closed subvarieties of arbitrary codimension. -/
theorem exists_periodic_scheme_point_lift
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] [IsIntegral X] [IsIntegral Y]
    (hcomm : g ≫ π = π ≫ f)
    (x : X) (s : ℕ) (hx : schemePointIterate f s x = x) :
    ∃ y : Y, π y = x ∧
      ∃ c : ℕ, 0 < c ∧ schemePointIterate g (s * c) y = y := by
  have hsemiconj : ∀ y : Y, π (g y) = f (π y) := by
    intro y
    exact congrArg (fun h : Y ⟶ X => h y) hcomm
  have hfinite : ∀ x : X, ((fun y : Y => π y) ⁻¹' {x}).Finite :=
    fun x => π.finite_preimage_singleton x
  obtain ⟨y, hy, c, hc, hcy⟩ :=
    exists_periodic_lift_of_surjective_finite_fibers
      (fun y : Y => g y) (fun x : X => f x) (fun y : Y => π y)
      hsemiconj π.surjective hfinite x s
      ((schemePointIterate_eq_function_iterate f s x).symm ▸ hx)
  exact ⟨y, hy, c, hc,
    (schemePointIterate_eq_function_iterate g (s * c) y).trans hcy⟩

#print axioms schemePointIterate_eq_function_iterate
#print axioms exists_periodic_scheme_point_lift

end Pcf
