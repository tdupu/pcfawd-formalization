/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingClosedSupports

/-!
# Proper closed subsets and normalization

Source-facing wrappers for `paper.tex`, `lem:finitely-many` and
`lem:normalization`. Divisors are actual codimension-one points with their
reduced closed supports. Normalization uses the actual canonical scheme map
and its lifted endomorphism, with all package inputs constructed geometrically.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf.PaperCharZero

/-- `lem:finitely-many`: a proper closed subset of an integral Noetherian scheme
contains only finitely many integral effective divisors, expressed by literal
containment of each divisor's closed support. -/
theorem finite_integral_effective_divisors_in_closed
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (Z : Set X) (hclosed : IsClosed Z) (hproper : Z ≠ Set.univ) :
    {D : SchemeDivisorPoint X | closure ({D.1} : Set X) ⊆ Z}.Finite := by
  apply (finite_schemeDivisorPoint_mem_of_isClosed hclosed hproper).subset
  intro D hD
  exact hD (subset_closure (Set.mem_singleton D.1))

/-- The same source finiteness statement with the divisor represented by its
actual reduced closed-subscheme immersion. -/
theorem finite_integral_effective_divisor_subschemes_in_closed
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (Z : Set X) (hclosed : IsClosed Z) (hproper : Z ≠ Set.univ) :
    {D : SchemeDivisorPoint X |
      Set.range (pointClosureIdealSheaf D.1).subschemeι ⊆ Z}.Finite := by
  apply (finite_schemeDivisorPoint_mem_of_isClosed hclosed hproper).subset
  intro D hD
  apply hD
  exact ⟨genericPoint (pointClosureIdealSheaf D.1).subscheme,
    pointClosureSubscheme_genericPoint D.1⟩

/-- Both assertions of `lem:normalization` for the actual canonical global
normalization. The upstairs PC set is computed using the actual lifted map and
its stalk ramification indices. The downstairs PC set is independently defined
by forward iterates. Normalization finiteness and finite divisor fibers are
proved inputs of the canonical package, not hypotheses of this theorem. -/
theorem normalization_postcritical_and_pcf
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    letI := charZero_stalk_of_field k s (genericPoint X)
    let D := schemeGlobalNormalizationUnnormalizedDynamicsOfFiniteType k s f
    D.postcriticalSet = D.normalization '' D.normalized.postcriticalSet ∧
      (D.IsPCF ↔ D.normalized.IsPCF) := by
  let := charZero_stalk_of_field k s (genericPoint X)
  let D := schemeGlobalNormalizationUnnormalizedDynamicsOfFiniteType k s f
  exact ⟨D.postcriticalSet_eq_normalization_image, D.isPCF_iff_normalized_isPCF⟩

end Pcf.PaperCharZero
