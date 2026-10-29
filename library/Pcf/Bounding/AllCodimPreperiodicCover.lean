/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimPeriodicCover
public import Pcf.Bounding.AllSubvarietyIteration

/-!
# Finite domination of a preperiodic subvariety return

The dimension induction for PCF along all subvariety chains passes from a
preperiodic centre to its periodic image. A periodic lift in a finite
commuting cover dominates a positive power of the return on that original
reduced image closure.
-/

@[expose] public section

namespace Pcf

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The actual return on the original reduced image closure of an
eventually periodic point has a positive power dominated by an upstairs
periodic point-closure return under any finite commuting cover. -/
theorem exists_preperiodic_pointClosure_cover
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] [IsIntegral X] [IsIntegral Y]
    (hcomm : g ≫ π = π ≫ f)
    (x : X) (r s : ℕ)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    let B := schemePointIterate f r x
    ∃ (y : Y) (_ : π y = B) (c : ℕ) (_ : 0 < c)
      (hy : schemePointIterate g (s * c) y = y),
      ∃ ρ : (pointClosureIdealSheaf y).subscheme ⟶
          (pointClosureIdealSheaf B).subscheme,
        IsFinite ρ ∧ IsDominant ρ ∧
          pointClosureReturnMap (End.of g ^ (s * c)).asHom y hy ≫ ρ =
            ρ ≫ (End.of (eventuallyPeriodicPointReturn f r s x h) ^ c).asHom := by
  let B := schemePointIterate f r x
  have hB : schemePointIterate f s B = B :=
    schemePointIterate_periodic f r s x h
  obtain ⟨y, hπ, c, hc, hy, hx', ρ, hρfin, hρdom, hcommρ⟩ :=
    exists_periodic_pointClosure_cover f g π hcomm B s hB
  refine ⟨y, hπ, c, hc, hy, ρ, hρfin, hρdom, ?_⟩
  calc
    pointClosureReturnMap (End.of g ^ (s * c)).asHom y hy ≫ ρ =
        ρ ≫ pointClosureReturnMap (End.of f ^ (s * c)).asHom B hx' := hcommρ
    _ = ρ ≫ (End.of (eventuallyPeriodicPointReturn f r s x h) ^ c).asHom := by
      rw [eventuallyPeriodicPointReturn_pow]
      rfl

#print axioms exists_preperiodic_pointClosure_cover

end

end Pcf
