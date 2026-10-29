/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPComponents
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# PCF and preperiodicity on the original variety

This file compares the three conditions in `paper-p.tex`, Proposition
`prop:pcf-equiv`, using the actual weighted branch and critical loci on a
possibly nonnormal variety.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

set_option linter.style.haveILetI false

private theorem finite_orbit_iff_preperiodic {α : Type*} (g : α → α) (x : α) :
    (Set.range (fun n : ℕ => g^[n] x)).Finite ↔
      ∃ r s : ℕ, 0 < s ∧ g^[r+s] x = g^[r] x := by
  constructor
  · intro h
    obtain ⟨r, n, hrn, heq⟩ :=
      h.exists_lt_map_eq_of_forall_mem (fun i : ℕ => Set.mem_range_self i)
    refine ⟨r, n - r, by omega, ?_⟩
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hrn)] using heq.symm
  · rintro ⟨r, s, hs, heq⟩
    let y := g^[r] x
    have hperiod : Function.IsPeriodicPt g s y := by
      change g^[s] y = y
      simpa only [y, ← Function.iterate_add_apply, Nat.add_comm] using heq
    let T : Set α := Set.range (fun i : Fin (r+s) => g^[i.val] x)
    have hT : T.Finite := Set.finite_range _
    apply hT.subset
    rintro z ⟨n, rfl⟩
    by_cases hn : n < r
    · exact ⟨⟨n, by omega⟩, rfl⟩
    · let m := n-r
      have hn' : n = r + m := by omega
      have hmod : g^[n] x = g^[r + (m % s)] x := by
        rw [hn', Nat.add_comm r m, Function.iterate_add_apply]
        rw [← hperiod.iterate_mod_apply m]
        rw [Nat.add_comm r (m % s), Function.iterate_add_apply]
      have hms : m % s < s := Nat.mod_lt _ hs
      exact ⟨⟨r + m % s, by omega⟩, hmod.symm⟩

private theorem finite_orbit_iff_tail_finite {α : Type*} (g : α → α) (x : α) :
    (Set.range (fun n : ℕ => g^[n] x)).Finite ↔
      (Set.range (fun n : ℕ => g^[n] (g x))).Finite := by
  have hdecomp :
      Set.range (fun n : ℕ => g^[n] x) =
        {x} ∪ Set.range (fun n : ℕ => g^[n] (g x)) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Set.mem_union_left _ (Set.mem_singleton x)
      | succ n =>
          apply Set.mem_union_right
          exact ⟨n, by
            change g^[n] (g x) = g^[n+1] x
            exact (Function.iterate_succ_apply g n x).symm⟩
    · intro h
      rcases h with h | ⟨n, rfl⟩
      · exact ⟨0, Set.mem_singleton_iff.mp h |>.symm⟩
      · exact ⟨n+1, by
          change g^[n+1] x = g^[n] (g x)
          exact Function.iterate_succ_apply g n x⟩
  rw [hdecomp]
  exact ⟨fun h => h.subset (Set.subset_union_right),
    fun h => (Set.finite_singleton x).union h⟩

private theorem iterate_image_pointClosure
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] (n : ℕ) (x : X) :
    (f : X → X)^[n] '' closure ({x} : Set X) =
      closure ({(f : X → X)^[n] x} : Set X) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ']
      change (fun y => f ((f : X → X)^[n] y)) '' closure ({x} : Set X) = _
      rw [← Set.image_image, ih]
      simpa only [Set.image_singleton, Function.comp_apply] using
        (f.isClosedMap.closure_image_eq_of_continuous f.continuous
          ({(f : X → X)^[n] x} : Set X)).symm

private theorem iterate_image_closure
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] (n : ℕ) (S : Set X) :
    (f : X → X)^[n] '' closure S =
      closure ((f : X → X)^[n] '' S) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (f : X → X)^[n + 1] '' closure S =
            f '' ((f : X → X)^[n] '' closure S) := by
          simp only [Function.iterate_succ', Set.image_comp]
        _ = f '' closure ((f : X → X)^[n] '' S) := by rw [ih]
        _ = closure (f '' ((f : X → X)^[n] '' S)) :=
          (f.isClosedMap.closure_image_eq_of_continuous f.continuous _).symm
        _ = closure ((f : X → X)^[n + 1] '' S) := by
          simp only [Function.iterate_succ', Set.image_comp]

private theorem finite_coheight_one_closure_injective
    {X : Scheme.{u}} {S T : Set X}
    (hS : S.Finite) (hT : T.Finite)
    (hcS : ∀ x ∈ S, Order.coheight x = 1)
    (hcT : ∀ x ∈ T, Order.coheight x = 1)
    (heq : closure S = closure T) : S = T := by
  have aux : ∀ (A B : Set X), A.Finite → B.Finite →
      (∀ x ∈ A, Order.coheight x = 1) →
      (∀ x ∈ B, Order.coheight x = 1) →
      closure A ⊆ closure B → A ⊆ B := by
    intro A B hA hB hcA hcB hAB x hx
    have hcl : x ∈ closure B := hAB (subset_closure hx)
    have hBcl : closure B = ⋃ y ∈ B, closure ({y} : Set X) := by
      calc
        closure B = closure (⋃ y ∈ B, ({y} : Set X)) := by
          rw [Set.biUnion_of_singleton]
        _ = ⋃ y ∈ B, closure ({y} : Set X) := hB.closure_biUnion _
    rw [hBcl] at hcl
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hcl
    have hle : x ≤ y :=
      (show y ⤳ x from specializes_iff_mem_closure.mpr hxy)
    by_cases hxy' : x = y
    · exact hxy' ▸ hy
    have hlt : x < y := lt_of_le_not_ge hle (fun hyx =>
      hxy' (Specializes.antisymm hyx hle).eq)
    have hc := Order.coheight_add_one_le hlt
    rw [hcA x hx, hcB y hy] at hc
    norm_num at hc
  exact Set.Subset.antisymm
    (aux S T hS hT hcS hcT heq.le)
    (aux T S hT hS hcT hcS heq.symm.le)

private theorem finite_union_iterates_iff_finite_range_image
    {α : Type*} (g : α → α) (B : Set α) (hB : B.Finite) :
    (⋃ n : ℕ, g^[n] '' B).Finite ↔
      (Set.range (fun n : ℕ => g^[n] '' B)).Finite := by
  constructor
  · intro h
    apply h.powerset.subset
    rintro S ⟨n, rfl⟩
    intro x hx
    exact Set.mem_iUnion.mpr ⟨n, hx⟩
  · intro h
    have hpart : ∀ S ∈ Set.range (fun n : ℕ => g^[n] '' B), S.Finite := by
      rintro S ⟨n, rfl⟩
      exact hB.image _
    have hU := h.biUnion hpart
    apply hU.subset
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨g^[n] '' B, Set.mem_iUnion.mpr
      ⟨⟨n, rfl⟩, hn⟩⟩

private theorem iterate_image_set {α : Type*} (g : α → α) (S : Set α) (n : ℕ) :
    (fun T : Set α => g '' T)^[n] S = g^[n] '' S := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Set.image_image]
      congr 1
      funext x
      exact (Function.iterate_succ_apply' g n x).symm

section Scheme
variable (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    (t : X ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]

private theorem branchPointSet_finite
    (hsep : IsGenericallySeparable f) :
    (weightedBranchPointSet f).Finite := by
  rw [weightedBranchPointSet_eq_image_criticalPointSet]
  exact (weightedCriticalPointSet_finite_of_lift_genericallySeparable f
    (isGenericallySeparable_schemeGlobalNormalizationMorphism f hsep)).image f

omit [NoetherianSpace X] in
include k t in
private theorem branchPoint_orbit_coheight_one
    (n : ℕ) {y : X} (hy : y ∈ weightedBranchPointSet f) :
    Order.coheight ((f : X → X)^[n] y) = 1 := by
  induction n with
  | zero => exact weightedBranchPointSet_coheight_one k t f hy
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k t f ⟨_, ih⟩

/-- The point-set form of `paper-p.tex`, Proposition `prop:pcf-equiv`,
conditions (1) and (2): PCF is equivalent to preperiodicity of each
weighted branch generic point on the original variety. -/
theorem weightedPostcriticalPointSet_finite_iff_branchPoint_preperiodic
    (hsep : IsGenericallySeparable f) :
    (weightedPostcriticalPointSet f).Finite ↔
      ∀ y ∈ weightedBranchPointSet f,
        ∃ r s : ℕ, 0 < s ∧ (f : X → X)^[r+s] y = (f : X → X)^[r] y := by
  have hset : weightedPostcriticalPointSet f =
      ⋃ y ∈ weightedBranchPointSet f,
        Set.range (fun n : ℕ => (f : X → X)^[n] y) := by
    ext y
    simp only [weightedPostcriticalPointSet, Set.mem_iUnion, Set.mem_image,
      Set.mem_range, exists_prop]
    tauto
  rw [hset]
  constructor
  · intro h y hy
    apply (finite_orbit_iff_preperiodic (f : X → X) y).mp
    exact h.subset (by
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨y, hy, hz⟩)
  · intro h
    exact (branchPointSet_finite f hsep).biUnion
      (fun y hy => (finite_orbit_iff_preperiodic (f : X → X) y).mpr (h y hy))

include k t in
/-- `paper-p.tex`, Proposition `prop:pcf-equiv`, conditions (1) and (2),
with the quantified objects the actual irreducible components of the
normalized weighted branch locus on the original variety.

`paper-p.tex` correspondence: item (2) of Proposition 5.1 (`item:orbits`). -/
theorem weightedPostcriticalPointSet_finite_iff_branchComponent_preperiodic
    (hsep : IsGenericallySeparable f) :
    (weightedPostcriticalPointSet f).Finite ↔
      ∀ D ∈ relativeIrreducibleComponents (weightedBranchLocus f),
        ∃ r s : ℕ, 0 < s ∧
          (f : X → X)^[r+s] '' D = (f : X → X)^[r] '' D := by
  rw [weightedPostcriticalPointSet_finite_iff_branchPoint_preperiodic f hsep]
  rw [weightedBranchLocus_components k t f hsep]
  constructor
  · intro h D hD
    obtain ⟨y, hy, rfl⟩ := hD
    obtain ⟨r, s, hs, heq⟩ := h y hy
    refine ⟨r, s, hs, ?_⟩
    rw [iterate_image_pointClosure f, iterate_image_pointClosure f, heq]
  · intro h y hy
    obtain ⟨r, s, hs, heq⟩ := h _ ⟨y, hy, rfl⟩
    rw [iterate_image_pointClosure f, iterate_image_pointClosure f] at heq
    refine ⟨r, s, hs, ?_⟩
    exact (isGenericPoint_closure : IsGenericPoint _
      (closure ({(f : X → X)^[r+s] y} : Set X))).eq
        (heq ▸ (isGenericPoint_closure : IsGenericPoint _
          (closure ({(f : X → X)^[r] y} : Set X))))

include k t in
private theorem weightedPostcriticalPointSet_finite_iff_branchLocus_orbit_finite
    (hsep : IsGenericallySeparable f) :
    (weightedPostcriticalPointSet f).Finite ↔
      (Set.range (fun n : ℕ => (f : X → X)^[n] '' weightedBranchLocus f)).Finite := by
  let B : ℕ → Set X := fun n => (f : X → X)^[n] '' weightedBranchPointSet f
  let L : ℕ → Set X := fun n => (f : X → X)^[n] '' weightedBranchLocus f
  have hbfin : (weightedBranchPointSet f).Finite := branchPointSet_finite f hsep
  have hpoint : (weightedPostcriticalPointSet f).Finite ↔ (Set.range B).Finite := by
    change (⋃ n, B n).Finite ↔ (Set.range B).Finite
    exact finite_union_iterates_iff_finite_range_image (f : X → X) _ hbfin
  have hclosure (n : ℕ) : L n = closure (B n) :=
    iterate_image_closure f n (weightedBranchPointSet f)
  have hcodim (n : ℕ) : ∀ y ∈ B n, Order.coheight y = 1 := by
    rintro y ⟨x, hx, rfl⟩
    exact branchPoint_orbit_coheight_one k t f n hx
  have hrange : Set.range L = closure '' Set.range B := by
    ext Z
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨B n, ⟨n, rfl⟩, (hclosure n).symm⟩
    · rintro ⟨A, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, hclosure n⟩
  have hinj : Set.InjOn closure (Set.range B) := by
    rintro A ⟨n, rfl⟩ C ⟨m, rfl⟩ h
    exact finite_coheight_one_closure_injective
      (hbfin.image _) (hbfin.image _) (hcodim n) (hcodim m) h
  constructor
  · intro h
    change (Set.range L).Finite
    rw [hrange]
    exact (hpoint.mp h).image _
  · intro h
    apply hpoint.mpr
    apply Set.Finite.of_finite_image _ hinj
    rw [← hrange]
    exact h

include k t in
/-- `paper-p.tex`, Proposition `prop:pcf-equiv`, conditions (1) and (3)
for the actual closed weighted critical locus on a possibly nonnormal
original variety. The equality is equality of underlying closed subsets,
matching the manuscript's reduced-locus convention.

`paper-p.tex` correspondence: item (3) of Proposition 5.1 (`item:crit-preperiodic`). -/
theorem weightedPostcriticalPointSet_finite_iff_criticalLocus_preperiodic
    (hsep : IsGenericallySeparable f) :
    (weightedPostcriticalPointSet f).Finite ↔
      ∃ r s : ℕ, 0 < s ∧
        (f : X → X)^[r+s] '' weightedCriticalLocus f =
          (f : X → X)^[r] '' weightedCriticalLocus f := by
  let F : Set X → Set X := fun S => f '' S
  have hbranch : F (weightedCriticalLocus f) = weightedBranchLocus f :=
    (weightedBranchLocus_eq_image_criticalLocus f).symm
  calc
    (weightedPostcriticalPointSet f).Finite ↔
        (Set.range (fun n : ℕ => (f : X → X)^[n] '' weightedBranchLocus f)).Finite :=
      weightedPostcriticalPointSet_finite_iff_branchLocus_orbit_finite k t f hsep
    _ ↔ (Set.range (fun n : ℕ => F^[n] (weightedBranchLocus f))).Finite := by
      simp only [F, iterate_image_set]
    _ ↔ (Set.range (fun n : ℕ => F^[n] (weightedCriticalLocus f))).Finite := by
      rw [← hbranch]
      exact (finite_orbit_iff_tail_finite F (weightedCriticalLocus f)).symm
    _ ↔ (∃ r s : ℕ, 0 < s ∧
        F^[r+s] (weightedCriticalLocus f) =
          F^[r] (weightedCriticalLocus f)) :=
      finite_orbit_iff_preperiodic F (weightedCriticalLocus f)
    _ ↔ (∃ r s : ℕ, 0 < s ∧
        (f : X → X)^[r+s] '' weightedCriticalLocus f =
          (f : X → X)^[r] '' weightedCriticalLocus f) := by
      simp only [F, iterate_image_set]

include k t in
/-- The three equivalent conditions of `paper-p.tex`, Proposition
`prop:pcf-equiv`, for a finite surjective separable self-map of a possibly
nonnormal variety. The branch components are actual irreducible components
of the weighted normalized branch locus. Set equality records the
manuscript's reduced closed-locus equality. -/
theorem paperP_pcf_equiv (hsep : IsGenericallySeparable f) :
    (IsWeightedNormalizedPCFDownstairs k t f ↔
      ∀ D ∈ relativeIrreducibleComponents (weightedBranchLocus f),
        ∃ r s : ℕ, 0 < s ∧
          (f : X → X)^[r+s] '' D = (f : X → X)^[r] '' D) ∧
    (IsWeightedNormalizedPCFDownstairs k t f ↔
      ∃ r s : ℕ, 0 < s ∧
        (f : X → X)^[r+s] '' weightedCriticalLocus f =
          (f : X → X)^[r] '' weightedCriticalLocus f) := by
  exact ⟨
    (isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k t f).trans
      (weightedPostcriticalPointSet_finite_iff_branchComponent_preperiodic k t f hsep),
    (isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k t f).trans
      (weightedPostcriticalPointSet_finite_iff_criticalLocus_preperiodic k t f hsep)⟩

end Scheme

/-- Proposition `prop:pcf-equiv` with normalization finiteness derived
from the variety's finite-type structure morphism.

`paper-p.tex` correspondence: Proposition 5.1 (`prop:pcf-equiv`), item (1) of Proposition 5.1
(`item:pcf`), item (2) of Proposition 5.1 (`item:orbits`), item (3) of Proposition 5.1
(`item:crit-preperiodic`). -/
theorem paperP_pcf_equiv_of_variety
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (t : X ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparable f) :
    (letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k t
    ((IsWeightedNormalizedPCFDownstairs k t f ↔
      ∀ D ∈ relativeIrreducibleComponents (weightedBranchLocus f),
        ∃ r s : ℕ, 0 < s ∧
          (f : X → X)^[r+s] '' D = (f : X → X)^[r] '' D) ∧
    (IsWeightedNormalizedPCFDownstairs k t f ↔
      ∃ r s : ℕ, 0 < s ∧
        (f : X → X)^[r+s] '' weightedCriticalLocus f =
          (f : X → X)^[r] '' weightedCriticalLocus f))) := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k t
  exact paperP_pcf_equiv k t f hsep

#print axioms weightedPostcriticalPointSet_finite_iff_branchPoint_preperiodic
#print axioms weightedPostcriticalPointSet_finite_iff_branchComponent_preperiodic
#print axioms weightedPostcriticalPointSet_finite_iff_criticalLocus_preperiodic
#print axioms paperP_pcf_equiv
#print axioms paperP_pcf_equiv_of_variety

end
end Pcf
