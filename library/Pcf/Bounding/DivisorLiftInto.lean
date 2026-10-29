/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.DivisorLift

/-!
# The "into" form of `lem:lift`

`Pcf.finiteDominantFiniteType_divisor_lift` states `lem:lift` for the canonical divisor
pushforward: it is surjective with finite fibres. The manuscript's finiteness clause is
about source divisors mapping *into* a target divisor `E`. This file bridges the two.

For a finite dominant morphism `f : X → Y` of integral schemes, `Y` of finite type over a
field, the image of the closure of a source divisor `D` is the closure of the image
divisor (finite morphisms are closed). If that image is contained in the closure of `E`,
then the generic point of `E` specializes to the image point; both have codimension one,
so they are equal and `D` maps onto `E`. Hence the divisors mapping into `E` are exactly
the fibre of the pushforward over `E`, which is finite.
-/

@[expose] public section

open TopologicalSpace
open AlgebraicGeometry

namespace Pcf

universe u

attribute [local instance] specializationOrder

section FiniteType

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y]
variable (k : Type*) [Field k]
  [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
  [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)]

/-- The image of the closure of a source divisor is the closure of its image divisor. -/
theorem SchemeDivisorPoint.image_closure_eq_closure_map (P : SchemeDivisorPoint X) :
    f '' closure ({P.1} : Set X) =
      closure ({(P.mapFiniteDominantFiniteType f k).1} : Set Y) := by
  calc
    f '' closure ({P.1} : Set X) = closure (f '' {P.1}) :=
      (f.isClosedMap.closure_image_eq_of_continuous f.continuous _).symm
    _ = closure ({(P.mapFiniteDominantFiniteType f k).1} : Set Y) := by
      simp only [Set.image_singleton, SchemeDivisorPoint.mapFiniteDominantFiniteType_val]

/-- A source divisor whose image lies in the closure of a target divisor `E` maps to `E`. -/
theorem SchemeDivisorPoint.map_eq_of_image_closure_subset (P : SchemeDivisorPoint X)
    (Q : SchemeDivisorPoint Y)
    (hP : f '' closure ({P.1} : Set X) ⊆ closure ({Q.1} : Set Y)) :
    P.mapFiniteDominantFiniteType f k = Q := by
  rw [SchemeDivisorPoint.image_closure_eq_closure_map f k] at hP
  have hmem : (P.mapFiniteDominantFiniteType f k).1 ∈ closure ({Q.1} : Set Y) :=
    hP (subset_closure (Set.mem_singleton _))
  have hle : (P.mapFiniteDominantFiniteType f k).1 ≤ Q.1 :=
    specializes_iff_mem_closure.mpr hmem
  by_contra hne
  have hneq : (P.mapFiniteDominantFiniteType f k).1 ≠ Q.1 := fun h => hne (Subtype.ext h)
  have hlt := Order.coheight_strictAnti (lt_of_le_of_ne hle hneq)
    (show Order.coheight Q.1 < ⊤ by
      rw [Q.2]
      exact ENat.natCast_lt_top 1)
  rw [(P.mapFiniteDominantFiniteType f k).2, Q.2] at hlt
  exact lt_irrefl _ hlt

include k in
/-- `lem:lift`, "into" form: let `f : X → Y` be a finite dominant (hence surjective)
morphism of integral schemes with `Y` of finite type over a field, and let `E` be an
integral effective divisor of `Y`. Some integral effective divisor `D` of `X` maps onto
`E`; every integral effective divisor `D` of `X` with `f(closure D) ⊆ closure E` maps
onto `E`; and only finitely many such `D` exist. Divisors are represented by their
codimension-one generic points and their closures.

Manuscript: `lem:lift` (Lemma 2.1). -/
theorem finiteDominantFiniteType_divisor_lift_into (Q : SchemeDivisorPoint Y) :
    (∃ P : SchemeDivisorPoint X, f '' closure ({P.1} : Set X) = closure ({Q.1} : Set Y)) ∧
      (∀ P : SchemeDivisorPoint X, f '' closure ({P.1} : Set X) ⊆ closure ({Q.1} : Set Y) →
        f '' closure ({P.1} : Set X) = closure ({Q.1} : Set Y)) ∧
      {P : SchemeDivisorPoint X |
        f '' closure ({P.1} : Set X) ⊆ closure ({Q.1} : Set Y)}.Finite := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := SchemeDivisorPoint.mapFiniteDominantFiniteType_surjective f k Q
    refine ⟨P, ?_⟩
    rw [SchemeDivisorPoint.image_closure_eq_closure_map f k]
    exact congrArg (fun D : SchemeDivisorPoint Y => closure ({D.1} : Set Y)) hP
  · intro P hP
    rw [SchemeDivisorPoint.image_closure_eq_closure_map f k,
      SchemeDivisorPoint.map_eq_of_image_closure_subset f k P Q hP]
  · apply (SchemeDivisorPoint.mapFiniteDominantFiniteType_finite_fiber f k Q).subset
    intro P hP
    exact SchemeDivisorPoint.map_eq_of_image_closure_subset f k P Q hP

end FiniteType

end Pcf

#print axioms Pcf.SchemeDivisorPoint.image_closure_eq_closure_map
#print axioms Pcf.SchemeDivisorPoint.map_eq_of_image_closure_subset
#print axioms Pcf.finiteDominantFiniteType_divisor_lift_into
