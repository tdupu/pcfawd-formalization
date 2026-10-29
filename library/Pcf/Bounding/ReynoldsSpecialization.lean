/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.CharP.Invertible

/-!
# Averaging invariant classes through a quotient

The proof of `lem:allcodim-monodromy` in `latex/paper-p.tex` uses
the Reynolds operator to identify the invariants after tensoring the
integral closure with a center's function field and then reducing.
This file proves the exactness step for an equivariant surjection of
modules when the group order is invertible. It is the algebraic
ingredient for lifting an invariant class modulo a stable ideal.
-/

@[expose] public section

namespace Pcf

universe u v w x

set_option linter.style.haveILetI false

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
  [CommRing k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

section InvertibleOrder

variable [Invertible (Fintype.card G : k)]

/-- Averaging commutes with a linear map intertwining two group actions. -/
theorem map_reynolds_of_intertwining
    (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W)
    (hcomm : ∀ g v, f (ρ g v) = σ g (f v))
    (v : V) :
    f (ρ.averageMap v) = σ.averageMap (f v) := by
  have hρ : ρ.averageMap v =
      ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
    simp [Representation.averageMap, GroupAlgebra.average]
  have hσ : σ.averageMap (f v) =
      ⅟(Fintype.card G : k) • ∑ g : G, σ g (f v) := by
    simp [Representation.averageMap, GroupAlgebra.average]
  rw [hρ, hσ, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => hcomm g v)

/-- For a finite group of invertible order, invariants lift through every
surjective equivariant linear map. Applied to a stable quotient, this is
the Reynolds exactness used in the proof of `paper-p.tex`,
Lemma `lem:allcodim-monodromy`. -/
theorem invariant_lift_of_surjective
    (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W) (hf : Function.Surjective f)
    (hcomm : ∀ g v, f (ρ g v) = σ g (f v))
    (w : W) (hw : w ∈ σ.invariants) :
    ∃ v : V, v ∈ ρ.invariants ∧ f v = w := by
  obtain ⟨v, rfl⟩ := hf w
  refine ⟨ρ.averageMap v, ρ.averageMap_invariant v, ?_⟩
  rw [map_reynolds_of_intertwining ρ σ f hcomm]
  exact σ.averageMap_id (f v) hw

end InvertibleOrder

/-- The prime-to-characteristic form of Reynolds exactness. The coprime
order condition supplies the inverse of the group order in the coefficient
field, exactly as in `paper-p.tex`, Lemma `lem:allcodim-monodromy`. -/
theorem invariant_lift_of_surjective_charP
    (p : ℕ) (hp : p.Prime) [CharP k p]
    (horder : (Fintype.card G).Coprime p)
    (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W) (hf : Function.Surjective f)
    (hcomm : ∀ g v, f (ρ g v) = σ g (f v))
    (w : W) (hw : w ∈ σ.invariants) :
    ∃ v : V, v ∈ ρ.invariants ∧ f v = w := by
  letI : Invertible (Fintype.card G : k) :=
    ((nonempty_invertible_iff_isUnit _).mpr
      ((CharP.isUnit_natCast_iff hp).mpr
        (hp.coprime_iff_not_dvd.mp horder.symm))).some
  exact invariant_lift_of_surjective ρ σ f hf hcomm w hw

#print axioms map_reynolds_of_intertwining
#print axioms invariant_lift_of_surjective
#print axioms invariant_lift_of_surjective_charP

end Pcf
