/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeLociCompare
public import Pcf.Bounding.PaperPIteration

/-!
# Coincidence of the three loci in codimension-one normal varieties

`paper-p.tex`, l. 2227–2229: if `A` and `B` are regular in codimension one,
then `branch(g) = branch₀(g) = branch₁(g)` (characteristic zero).
`paper-p.tex`, l. 2375–2378: `PC(f) ⊆ PC₀(f) ⊆ PC₁(f)`, and when `X` is
regular in codimension one the three notions of PCF coincide.

Divisors are represented by their generic points (convention C1), so the
equalities below are equalities of the sets of generic points of the
integral effective divisors constituting the loci. "Regular in codimension
one" enters only through integral closedness of the local rings at
codimension-one points; for a one-dimensional Noetherian local domain this
is equivalent to regularity (both mean DVR), so the hypothesis is the
source's.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

private theorem end_pow_apply_eq_iterate'
    {X : Scheme.{u}} (f : X ⟶ X) (m : ℕ) (x : X) :
    (End.of f ^ m).asHom x = (f : X → X)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [pow_succ', End.mul_asHom, Scheme.Hom.comp_apply,
        Function.iterate_succ_apply', ih]

section Loci

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]

include k sX sY in
/-- **l. 2227–2229, critical level.** In characteristic zero, if the local
rings of `A` and `B` at codimension-one points are normal (regular in
codimension one), then `crit(g) = crit₀(g) = crit₁(g)`, as sets of generic
points of integral effective divisors. -/
theorem weightedCriticalPointSet_eq_unnormalized_of_codimOne_normal
    (hX : ∀ P : SchemeDivisorPoint X, IsIntegrallyClosed (X.presheaf.stalk P.1))
    (hY : ∀ Q : SchemeDivisorPoint Y, IsIntegrallyClosed (Y.presheaf.stalk Q.1)) :
    weightedCriticalPointSet g =
        {x : X | ∃ P : SchemeDivisorPoint X, P.1 = x ∧ P ∈ schemeUnnormalizedCriticalZero g} ∧
    {x : X | ∃ P : SchemeDivisorPoint X, P.1 = x ∧ P ∈ schemeUnnormalizedCriticalZero g} =
        {x : X | ∃ P : SchemeDivisorPoint X, P.1 = x ∧ P ∈ schemeUnnormalizedCriticalOne g} := by
  have hcmp (P : SchemeDivisorPoint X) :=
    weightedCriticalPoint_iff_unnormalized_of_normal_stalks g k sY P (hX P)
      (hY ⟨g P.1, coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sY g P⟩)
  constructor
  · apply Set.Subset.antisymm
    · exact weightedCriticalPointSet_subset_schemeUnnormalizedCriticalZero g k sX sY
    · rintro x ⟨P, rfl, hP⟩
      exact (hcmp P).1.mpr hP
  · ext x
    constructor
    · rintro ⟨P, rfl, hP⟩
      exact ⟨P, rfl, (hcmp P).2.mp hP⟩
    · rintro ⟨P, rfl, hP⟩
      exact ⟨P, rfl, (hcmp P).2.mpr hP⟩

include k sX sY in
/-- **l. 2227–2229.** In characteristic zero, if `A` and `B` are regular
(equivalently normal) in codimension one, then
`branch(g) = branch₀(g) = branch₁(g)`, as sets of generic points of the
integral effective divisors of `B` constituting the loci. -/
theorem weightedBranchPointSet_eq_unnormalized_of_codimOne_normal
    (hX : ∀ P : SchemeDivisorPoint X, IsIntegrallyClosed (X.presheaf.stalk P.1))
    (hY : ∀ Q : SchemeDivisorPoint Y, IsIntegrallyClosed (Y.presheaf.stalk Q.1)) :
    weightedBranchPointSet g =
        {y : Y | ∃ E ∈ schemeUnnormalizedBranchZero g, E.1 = y} ∧
    {y : Y | ∃ E ∈ schemeUnnormalizedBranchZero g, E.1 = y} =
        {y : Y | ∃ E ∈ schemeUnnormalizedBranchOne g, E.1 = y} := by
  letI (U : Y.affineOpens) := schemeAffineAlgebraOfField k sY U
  letI (U : Y.affineOpens) := schemeAffineAlgebraOfField_finiteType k sY U
  obtain ⟨h0, h1⟩ := weightedCriticalPointSet_eq_unnormalized_of_codimOne_normal
    g k sX sY hX hY
  have himage (C : Set (SchemeDivisorPoint X)) :
      {y : Y | ∃ E ∈ (fun P : SchemeDivisorPoint X =>
          P.mapFiniteDominantFiniteType g k) '' C, E.1 = y} =
        g '' {x : X | ∃ P : SchemeDivisorPoint X, P.1 = x ∧ P ∈ C} := by
    ext y
    constructor
    · rintro ⟨_, ⟨P, hP, rfl⟩, rfl⟩
      exact ⟨P.1, ⟨P, rfl, hP⟩, rfl⟩
    · rintro ⟨_, ⟨P, rfl, hP⟩, rfl⟩
      exact ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  rw [schemeUnnormalizedBranchZero_eq_image_critical g k,
    schemeUnnormalizedBranchOne_eq_image_critical g k, himage, himage,
    weightedBranchPointSet_eq_image_criticalPointSet, h0, h1]
  exact ⟨rfl, rfl⟩

end Loci

private theorem finite_iff_val_image {X : Scheme.{u}} (S : Set (SchemeDivisorPoint X)) :
    S.Finite ↔ (Subtype.val '' S).Finite :=
  ⟨fun h => h.image _, fun h => h.of_finite_image Subtype.val_injective.injOn⟩

section Postcritical

variable (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]

omit [CharZero k] [NoetherianSpace X] in
/-- Generic points of the members of `PC_i(f)`. -/
private theorem unnormalizedPostcritical_points (i : Bool) :
    Subtype.val '' schemeUnnormalizedPostcriticalSet i k s f =
      ⋃ n : ℕ, (f : X → X)^[n] '' {y : X | ∃ E ∈ schemeUnnormalizedBranch i f, E.1 = y} := by
  ext x
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨n, E, hE, rfl⟩ := Set.mem_iUnion.mp hD
    refine Set.mem_iUnion.mpr ⟨n, E.1, ⟨E, hE, rfl⟩, ?_⟩
    rw [schemeDivisorIterateOfFiniteType_val]
    exact (end_pow_apply_eq_iterate' f n E.1).symm
  · intro hx
    obtain ⟨n, _, ⟨E, hE, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨_, Set.mem_iUnion.mpr ⟨n, E, hE, rfl⟩, ?_⟩
    rw [schemeDivisorIterateOfFiniteType_val]
    exact end_pow_apply_eq_iterate' f n E.1

omit [NoetherianSpace X] in
/-- **l. 2375–2376, first inclusion.** In characteristic zero, the generic
points of `PC(f)` are generic points of members of `PC₀(f)`. -/
theorem weightedPostcriticalPointSet_subset_unnormalizedZero :
    letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
    weightedPostcriticalPointSet f ⊆
      Subtype.val '' schemeUnnormalizedPostcriticalSet false k s f := by
  letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField k s U
  rw [unnormalizedPostcritical_points]
  refine Set.iUnion_mono fun n => Set.image_mono ?_
  intro y hy
  obtain ⟨E, h1, h2⟩ :=
    weightedBranchPointSet_subset_schemeUnnormalizedBranchZero_points f k s s hy
  exact ⟨E, by simpa [schemeUnnormalizedBranch] using h2, h1⟩

/-- **l. 2375–2378.** In characteristic zero, if `X` is regular (equivalently
normal) in codimension one, then `PC(f)`, `PC₀(f)` and `PC₁(f)` have the same
generic points, and PCF, `0`-PCF and `1`-PCF coincide. -/
theorem postcritical_coincide_of_codimOne_normal
    (hX : ∀ P : SchemeDivisorPoint X, IsIntegrallyClosed (X.presheaf.stalk P.1)) :
    letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
    (weightedPostcriticalPointSet f =
        Subtype.val '' schemeUnnormalizedPostcriticalSet false k s f ∧
      Subtype.val '' schemeUnnormalizedPostcriticalSet false k s f =
        Subtype.val '' schemeUnnormalizedPostcriticalSet true k s f) ∧
    (IsWeightedNormalizedPCFDownstairs k s f ↔ IsSchemeUnnormalizedPCF false k s f) ∧
    (IsSchemeUnnormalizedPCF false k s f ↔ IsSchemeUnnormalizedPCF true k s f) := by
  letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
  obtain ⟨h0, h1⟩ := weightedBranchPointSet_eq_unnormalized_of_codimOne_normal
    f k s s hX hX
  have hpts : weightedPostcriticalPointSet f =
        Subtype.val '' schemeUnnormalizedPostcriticalSet false k s f ∧
      Subtype.val '' schemeUnnormalizedPostcriticalSet false k s f =
        Subtype.val '' schemeUnnormalizedPostcriticalSet true k s f := by
    rw [unnormalizedPostcritical_points, unnormalizedPostcritical_points]
    simp only [schemeUnnormalizedBranch, Bool.false_eq_true, ↓reduceIte]
    rw [← h1, ← h0]
    exact ⟨rfl, rfl⟩
  refine ⟨hpts, ?_, ?_⟩
  · rw [isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite,
      IsSchemeUnnormalizedPCF, finite_iff_val_image, ← hpts.1]
  · rw [IsSchemeUnnormalizedPCF, IsSchemeUnnormalizedPCF, finite_iff_val_image,
      finite_iff_val_image, hpts.2]

end Postcritical

#print axioms weightedCriticalPointSet_eq_unnormalized_of_codimOne_normal
#print axioms weightedBranchPointSet_eq_unnormalized_of_codimOne_normal
#print axioms weightedPostcriticalPointSet_subset_unnormalizedZero
#print axioms postcritical_coincide_of_codimOne_normal

end

end Pcf
