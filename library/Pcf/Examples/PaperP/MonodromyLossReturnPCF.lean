/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossReturnScheme
public import Pcf.Examples.PaperP.BasilicaProjectivePCF
public import Pcf.Bounding.TheoremADivisors

/-!
# The return of `ex:monodromy-loss` is PCF

For `latex/paper-p.tex`, Example `ex:monodromy-loss`, in characteristic `3`
with `i² = -1`: the actual degree-four return `g : ℙ¹ ⟶ ℙ¹` is generically
separable, its normalization-weighted critical point set is exactly `{0}`
("its only critical point is `0`"), its branch set is `{∞}`, its
postcritical set is `{∞}` (`0 ↦ ∞ ↦ ∞`), and it satisfies the manuscript's
normalized PCF predicates `Pcf.IsWeightedNormalizedPCFDownstairs` and
`Pcf.IsSeparableNormalizedPCF`, as well as the ramification-index predicate
`Pcf.Palomar.IsPCF`.

The source's reason for separability ("its derivative is the nonzero
constant `-i`") appears here as the Jacobian determinant `-i u⁶`, which is
nonzero at the generic point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.MonodromyLossReturn
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type*) [Field k] {i : k} (hi : i ^ 2 = -1) [CharP k 3]
include hi

local notation "zero" => BasilicaProjectiveScheme.zero k
local notation "infinity" => BasilicaProjectiveScheme.infinity k

local instance normalizationIso :
    IsIso (Pcf.Palomar.normalizationMap (Proj (grading k))) :=
  Pcf.normalScheme_normalizationMap_isIso _

/-- A source divisor has weighted local degree greater than one exactly at `0`. -/
theorem divisorDelta_gt_one_iff (d : Pcf.SchemeDivisorPoint (Proj (grading k))) :
    1 < Pcf.schemeDivisorDelta (schemeMap k i hi) d ↔ d.1 = zero := by
  have hd : Pcf.schemeDivisorDelta (schemeMap k i hi) d = 1 ↔
      Pcf.Stacks.IsStacksEtaleAt (schemeMap k i hi) d.1 := by
    rw [Pcf.paperP_divisorDelta_eq_one_iff_etaleAt]
    constructor
    · rintro ⟨V, hV, U, hU, hUV, hp, he⟩
      exact ⟨U, hU, V, hV, hUV, hp, he⟩
    · rintro ⟨U, hU, V, hV, hUV, hp, he⟩
      exact ⟨V, hV, U, hU, hUV, hp, he⟩
  rw [etaleAt_iff k hi] at hd
  have hpos := Pcf.schemeDivisorDelta_pos_of_isFinite (schemeMap k i hi) d
  constructor
  · intro h
    by_contra he
    have h1 := hd.mpr he
    omega
  · intro he
    have hn : Pcf.schemeDivisorDelta (schemeMap k i hi) d ≠ 1 := fun h1 => hd.mp h1 he
    omega

/-- **"Its only critical point is `0`."** The canonical-normalization weighted
critical generic-point set of the actual return is exactly `{0}`. -/
theorem weightedCriticalPointSet_eq :
    Pcf.weightedCriticalPointSet (schemeMap k i hi) = {zero} := by
  rw [Pcf.weightedCriticalPointSet_eq_schemeDelta_of_normal]
  ext p
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (divisorDelta_gt_one_iff k hi d).mp hd
  · rintro rfl
    exact ⟨BasilicaProjectiveScheme.zeroDivisor k,
      (divisorDelta_gt_one_iff k hi _).mpr rfl, rfl⟩

/-- The weighted branch generic-point set is `{∞}`. -/
theorem weightedBranchPointSet_eq :
    Pcf.weightedBranchPointSet (schemeMap k i hi) = {infinity} := by
  rw [Pcf.weightedBranchPointSet_eq_image_criticalPointSet, weightedCriticalPointSet_eq k hi,
    Set.image_singleton, zero_to_infinity]

/-- **`0 ↦ ∞ ↦ ∞`.** The weighted postcritical generic-point set is `{∞}`. -/
theorem weightedPostcriticalPointSet_eq :
    Pcf.weightedPostcriticalPointSet (schemeMap k i hi) = {infinity} := by
  rw [Pcf.weightedPostcriticalPointSet, weightedBranchPointSet_eq k hi]
  ext q
  simp only [Set.image_singleton, Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact iterate_infinity k hi n
  · rintro rfl
    exact ⟨0, rfl⟩

/-- The closed weighted critical locus is `{0}`. -/
theorem weightedCriticalLocus_eq :
    Pcf.weightedCriticalLocus (schemeMap k i hi) = {zero} := by
  rw [Pcf.weightedCriticalLocus, weightedCriticalPointSet_eq k hi,
    (BasilicaProjectiveScheme.zero_isClosed k).closure_eq]

/-- The closed weighted branch locus is `{∞}`. -/
theorem weightedBranchLocus_eq :
    Pcf.weightedBranchLocus (schemeMap k i hi) = {infinity} := by
  rw [Pcf.weightedBranchLocus, weightedBranchPointSet_eq k hi,
    (BasilicaProjectiveScheme.infinity_isClosed k).closure_eq]

/-- **"The map `g` is separable."** The actual function-field extension of the
return is separable: the generic stalk map is formally étale since the
Jacobian `-i u⁶` does not vanish at the generic point. -/
theorem isGenericallySeparable : Pcf.IsGenericallySeparable (schemeMap k i hi) := by
  apply Pcf.isGenericallySeparable_of_formallyEtale_generic
  apply stalk_formallyEtale_of_ne k hi
  intro he
  have h0 : Order.coheight (genericPoint (Proj (grading k))) = 0 := by
    change Order.coheight (⊤ : Proj (grading k)) = 0
    exact Order.coheight_top _
  rw [he, BasilicaProjectiveScheme.zero_coheight] at h0
  norm_num at h0

/-- The manuscript's normalized weighted PCF predicate for the actual return. -/
theorem isWeightedNormalizedPCF :
    Pcf.IsWeightedNormalizedPCFDownstairs k (BasilicaProjectiveScheme.structureMap k)
      (schemeMap k i hi) := by
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    k (BasilicaProjectiveScheme.structureMap k) (schemeMap k i hi)).mpr
  rw [weightedPostcriticalPointSet_eq k hi]
  exact Set.finite_singleton _

/-- **"Thus `g` remains PCF."** The actual return satisfies the ambient separable
normalized PCF predicate, the root of `def:pcfawd`. -/
theorem isSeparableNormalizedPCF :
    Pcf.IsSeparableNormalizedPCF k (BasilicaProjectiveScheme.structureMap k)
      (schemeMap k i hi) :=
  (Pcf.isSeparableNormalizedPCF_iff_downstairs k _ _).mpr
    ⟨isGenericallySeparable k hi, isWeightedNormalizedPCF k hi⟩

/-! ### The ramification-index PCF predicate -/

/-- The actual stalk ramification index is one away from `0`. -/
theorem ramificationIndexAt_eq_one_of_ne (p : Proj (grading k)) (hp : p ≠ zero) :
    Pcf.Palomar.ramificationIndexAt (schemeMap k i hi) p = 1 := by
  have hfe := stalk_formallyEtale_of_ne k hi p hp
  letI := ((schemeMap k i hi).stalkMap p).hom.toAlgebra
  haveI : Algebra.FormallyEtale
      ((Proj (grading k)).presheaf.stalk (schemeMap k i hi p))
      ((Proj (grading k)).presheaf.stalk p) :=
    RingHom.formallyEtale_algebraMap.mp hfe
  haveI : Algebra.EssFiniteType
      ((Proj (grading k)).presheaf.stalk (schemeMap k i hi p))
      ((Proj (grading k)).presheaf.stalk p) :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap (schemeMap k i hi) p)
  exact Ideal.ramificationIdx_eq_one _ _

/-- The ramification-index postcritical set is contained in `{∞}`. -/
theorem postcriticalSet_subset :
    Pcf.Palomar.postcriticalSet (schemeMap k i hi) ⊆ {infinity} := by
  rintro y ⟨p, _, hr, n, rfl⟩
  by_cases hp : p = zero
  · subst hp
    rw [Function.iterate_succ_apply, zero_to_infinity, iterate_infinity]
    rfl
  · have h1 := ramificationIndexAt_eq_one_of_ne k hi p hp
    omega

/-- The actual return is ramification-index PCF. -/
theorem isPCF : Pcf.Palomar.IsPCF (schemeMap k i hi) :=
  (Set.finite_singleton _).subset (postcriticalSet_subset k hi)

#print axioms divisorDelta_gt_one_iff
#print axioms weightedCriticalPointSet_eq
#print axioms weightedBranchPointSet_eq
#print axioms weightedPostcriticalPointSet_eq
#print axioms weightedCriticalLocus_eq
#print axioms weightedBranchLocus_eq
#print axioms isGenericallySeparable
#print axioms isWeightedNormalizedPCF
#print axioms isSeparableNormalizedPCF
#print axioms ramificationIndexAt_eq_one_of_ne
#print axioms isPCF

end Pcf.Examples.PaperP.MonodromyLossReturn
