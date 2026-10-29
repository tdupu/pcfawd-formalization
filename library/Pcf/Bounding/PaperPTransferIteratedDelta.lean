/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeFiniteResidueDelta

/-!
# Iterated weighted-degree equation in `paper-p.tex`

This is equation `eq:transfer-iterated-delta` for the actual commuting
finite scheme square and every iterate, with the manuscript's factor order.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u

set_option linter.style.haveILetI false

theorem paperP_commutingSquare_iterate
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    (hcomm : g ≫ π = π ≫ f) (n : ℕ) :
    (End.of g ^ n).asHom ≫ π = π ≫ (End.of f ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (g ≫ (End.of g ^ n).asHom) ≫ π =
        π ≫ (f ≫ (End.of f ^ n).asHom)
      rw [Category.assoc, ih, ← Category.assoc, hcomm, Category.assoc]

/-- `paper-p.tex`, equation `eq:transfer-iterated-delta`, on the actual
finite normal schemes and categorical iterates.

`paper-p.tex` correspondence: equation (4) (`eq:transfer-iterated-delta`). -/
theorem paperP_transfer_iterated_delta
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f) (d : SchemeDivisorPoint Y) (n : ℕ) :
    let F := (End.of f ^ n).asHom
    let G := (End.of g ^ n).asHom
    letI : IsFinite F := isFinite_end_pow f n
    letI : IsDominant F := isDominant_end_pow f n
    letI : IsFinite G := isFinite_end_pow g n
    letI : IsDominant G := isDominant_end_pow g n
    schemeDivisorDelta π d * schemeDivisorDelta F (d.mapFiniteDominantNormal π) =
      schemeDivisorDelta G d *
        schemeDivisorDelta π (d.mapFiniteDominantNormal G) := by
  have h := schemeDeltaDynamics_comparison_tower_of_isFinite
    (End.of f ^ n).asHom (End.of g ^ n).asHom π
    (paperP_commutingSquare_iterate f g π hcomm n) d
  simpa only [mul_comm] using h

#print axioms paperP_commutingSquare_iterate
#print axioms paperP_transfer_iterated_delta

end Pcf
