/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupConstructionAffine

/-!
# Finite families of branch divisors on a fixed normalized blow-up

The final tower argument needs a finite family `W` on one fixed target
normalized blow-up. The exceptional divisor generic points are finite.
Away from them, finite fibers over the finite ambient branch family make
the union of every lifted branch support finite, regardless of how many
covers occur in the tower.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- A finite exceptional set and finite off-exceptional fibers over a finite
ambient branch family yield one finite family of lifted branch points. -/
theorem finite_union_of_lifted_branch_sets
    {A B : Type*} (β : A → B)
    (Exceptional : Set A) (hExceptional : Exceptional.Finite)
    (Ambient : Set B) (hAmbient : Ambient.Finite)
    (hfiber : ∀ y ∈ Ambient,
      {x : A | x ∉ Exceptional ∧ β x = y}.Finite)
    (branch : ℕ → Set A)
    (hbranch : ∀ n x, x ∈ branch n →
      x ∈ Exceptional ∨ β x ∈ Ambient) :
    (⋃ n, branch n).Finite := by
  let Lifted : Set A :=
    ⋃ y ∈ Ambient, {x : A | x ∉ Exceptional ∧ β x = y}
  have hLifted : Lifted.Finite :=
    hAmbient.biUnion (fun y hy => hfiber y hy)
  apply (hExceptional.union hLifted).subset
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  rcases hbranch n x hn with he | ha
  · exact Or.inl he
  · by_cases he : x ∈ Exceptional
    · exact Or.inl he
    · exact Or.inr (Set.mem_biUnion ha ⟨he, rfl⟩)

/-- Pointwise injectivity away from the exceptional points implies the
finite-fiber premise used above. -/
theorem finite_offExceptional_fiber_of_injOn
    {A B : Type*} (β : A → B) (Exceptional : Set A)
    (hinj : Set.InjOn β Exceptionalᶜ) (y : B) :
    {x : A | x ∉ Exceptional ∧ β x = y}.Finite := by
  apply Set.Finite.of_injOn
    (s := {x : A | x ∉ Exceptional ∧ β x = y})
    (t := {y}) (f := β)
  · intro x hx
    exact hx.2
  · intro x hx x' hx' h
    exact hinj hx.1 hx'.1 h
  · exact Set.finite_singleton y

/-- For the actual normalized Rees target, only the finite off-exceptional
fibers above ambient branch points remain to construct `W`. -/
theorem normalizedRees_lifted_branch_family_finite_of_finiteFibers
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (Ambient : Set (Spec (.of R))) (hAmbient : Ambient.Finite)
    (hfiber :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let β := normalizedReesProjToSpec I a ha
      let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
        {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
      ∀ y ∈ Ambient,
        {D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) |
          D ∉ Exceptional ∧ β D.1 = y}.Finite)
    (branch :
      (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
       ℕ → Set (SchemeDivisorPoint (Palomar.normalization (reesProj I)))))
    (hbranch :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let β := normalizedReesProjToSpec I a ha
      let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
        {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
      ∀ n D, D ∈ branch n → D ∈ Exceptional ∨ β D.1 ∈ Ambient) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (⋃ n, branch n).Finite) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
    {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
  have hExceptional : Exceptional.Finite :=
    normalizedReesExceptional_divisorPoints_finite k I hI a ha
  exact finite_union_of_lifted_branch_sets
    (fun D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) => β D.1)
    Exceptional hExceptional Ambient hAmbient hfiber branch hbranch

#print axioms finite_union_of_lifted_branch_sets
#print axioms finite_offExceptional_fiber_of_injOn
#print axioms normalizedRees_lifted_branch_family_finite_of_finiteFibers

end
end Pcf.Bounding.AllCodimBlowup
