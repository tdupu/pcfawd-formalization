/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimPeriodicLift
public import Pcf.Bounding.PcfAllTheWayDownScheme

/-!
# Finite domination of a periodic point-closure return

For a finite commuting cover, a periodic point downstairs has a periodic
point above it. Restricting the cover to their original reduced closures
gives a finite dominant comparison of the corresponding return maps.
-/

@[expose] public section

namespace Pcf

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The periodic lift of a point under a finite commuting cover gives a
finite dominant map between the original reduced point closures, and that
map intertwines the actual return morphisms. -/
theorem exists_periodic_pointClosure_cover
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] [IsIntegral X] [IsIntegral Y]
    (hcomm : g ≫ π = π ≫ f)
    (x : X) (s : ℕ) (hx : schemePointIterate f s x = x) :
    ∃ (y : Y) (_ : π y = x) (c : ℕ) (_ : 0 < c)
      (hy : schemePointIterate g (s * c) y = y)
      (hx' : schemePointIterate f (s * c) x = x),
      ∃ ρ : (pointClosureIdealSheaf y).subscheme ⟶
          (pointClosureIdealSheaf x).subscheme,
        IsFinite ρ ∧ IsDominant ρ ∧
          pointClosureReturnMap (End.of g ^ (s * c)).asHom y hy ≫ ρ =
            ρ ≫ pointClosureReturnMap (End.of f ^ (s * c)).asHom x hx' := by
  obtain ⟨y, hπ, c, hc, hy⟩ :=
    exists_periodic_scheme_point_lift f g π hcomm x s hx
  have hx' : schemePointIterate f (s * c) x = x := by
    change (End.of f ^ (s * c)).asHom x = x
    rw [pow_mul]
    exact end_pow_apply_eq_of_apply_eq (End.of f ^ s).asHom x hx c
  let ρ := pointClosureSubschemeMap π y x hπ
  haveI : IsFinite ρ := pointClosureSubschemeMap_isFinite π y x hπ
  haveI : IsDominant ρ := pointClosureSubschemeMap_isDominant π y x hπ
  refine ⟨y, hπ, c, hc, hy, hx', ρ, inferInstance, inferInstance, ?_⟩
  exact pointClosureSubschemeMap_comm
    (End.of f ^ (s * c)).asHom (End.of g ^ (s * c)).asHom π
    (normalization_square_pow f g π hcomm (s * c))
    x y hx' hy hπ

#print axioms exists_periodic_pointClosure_cover

end

end Pcf
