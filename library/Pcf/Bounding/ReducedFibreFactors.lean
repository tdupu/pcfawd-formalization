/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.InvariantBaseChange
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Field factors of a reduced finite fibre

The reduced fibre `C_red` in `latex/paper-p.tex`, Lemma
`lem:allcodim-monodromy`, is a finite reduced algebra over the
function field of the centre. It is a product of its residue fields
at maximal ideals. When its invariant algebra is the base field,
the group permutes those factors transitively.
-/

@[expose] public section

namespace Pcf

universe u v w

open scoped Pointwise
set_option linter.style.haveILetI false

variable {F : Type u} {A : Type v} {G : Type w}
  [Field F] [CommRing A] [Algebra F A]
  [Group G] [Finite G]

section ReducedFinite

variable [FiniteDimensional F A] [IsReduced A]

/-- The actual finite reduced fibre is the product of its residue
fields at maximal ideals. -/
noncomputable def reducedFiniteAlgebraEquivPi :
    A ≃ₐ[A] ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite F A
  exact IsArtinianRing.equivPi A

end ReducedFinite

/-- Every factor of the reduced fibre is a field. -/
theorem reducedFiniteAlgebra_factor_isField (m : MaximalSpectrum A) :
    IsField (A ⧸ m.asIdeal) := by
  letI : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact Field.toIsField _

/-- If the invariant algebra is the base field, any two field
components of the reduced fibre lie in the same `G`-orbit.
This is the transitivity step in `lem:allcodim-monodromy`. -/
theorem reducedFiniteAlgebra_factors_transitive
    [MulSemiringAction G A] [SMulCommClass G F A]
    [Algebra.IsInvariant F A G]
    (m n : MaximalSpectrum A) :
    ∃ g : G, n.asIdeal = g • m.asIdeal := by
  have hm : (m.asIdeal.under F).IsPrime := inferInstance
  have hn : (n.asIdeal.under F).IsPrime := inferInstance
  have hunder : m.asIdeal.under F = n.asIdeal.under F := by
    rw [Ideal.eq_bot_of_prime (m.asIdeal.under F),
      Ideal.eq_bot_of_prime (n.asIdeal.under F)]
  exact Algebra.IsInvariant.exists_smul_of_under_eq F A G
    m.asIdeal n.asIdeal hunder

#print axioms reducedFiniteAlgebraEquivPi
#print axioms reducedFiniteAlgebra_factors_transitive

end Pcf
