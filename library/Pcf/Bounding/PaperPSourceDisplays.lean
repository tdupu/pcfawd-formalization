/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPPCFEquiv

/-!
# Exact displayed set identities of `paper-p.tex`

The enclosing results are formalized elsewhere; this file states the
displayed identities themselves on the actual closed weighted loci of the
original (possibly nonnormal) variety, under the review's conventions C1–C5.

* l. 492–498 (after `def:pcf`): the union of the postcritical divisors is the
  forward orbit of the branch locus and the strict forward orbit of the
  critical locus; each member of `PC(f)` is a divisor, `f` carries members to
  members, and the union is closed when `f` is PCF.
* Display l. 922 (proof of `prop:pcf-equiv`, (2) ⇒ (3)): the critical-locus
  chain with `r = 1 + max rᵢ`, `s = lcm sᵢ`.
* Display l. 1061 (proof of `lem:covers`): the branch identity from
  `lem:tower` on both sides of the commuting square, its containment in
  `T = π(PC(g)) ∪ branch(π)`, and forward invariance of `T`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- A preperiodicity relation `g^[a+b] '' D = g^[a] '' D` persists past `a`
and along multiples of `b`. -/
theorem iterate_image_preperiodic_add_mul {α : Type*} (g : α → α) (D : Set α)
    (a b : ℕ) (h : g^[a + b] '' D = g^[a] '' D) :
    ∀ n, a ≤ n → ∀ m, g^[n + m * b] '' D = g^[n] '' D := by
  have hstep : ∀ n, a ≤ n → g^[n + b] '' D = g^[n] '' D := by
    intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    calc g^[a + j + b] '' D = g^[j] '' (g^[a + b] '' D) := by
          rw [← Set.image_comp, ← Function.iterate_add]; congr 2; omega
      _ = g^[j] '' (g^[a] '' D) := by rw [h]
      _ = g^[a + j] '' D := by
          rw [← Set.image_comp, ← Function.iterate_add]; congr 2; omega
  intro n hn m
  induction m with
  | zero => simp
  | succ m ih =>
      calc g^[n + (m + 1) * b] '' D = g^[(n + m * b) + b] '' D := by
            congr 2; ring
        _ = g^[n + m * b] '' D := hstep _ (le_trans hn (Nat.le_add_right _ _))
        _ = g^[n] '' D := ih

/-- A preperiodicity relation `g^[a+b] '' D = g^[a] '' D` gives
`g^[n+S] '' D = g^[n] '' D` for every `n ≥ a` and every multiple `S` of `b`. -/
theorem iterate_image_preperiodic_of_dvd {α : Type*} (g : α → α) (D : Set α)
    (a b : ℕ) (h : g^[a + b] '' D = g^[a] '' D) (n : ℕ) (hn : a ≤ n)
    (S : ℕ) (hS : b ∣ S) : g^[n + S] '' D = g^[n] '' D := by
  obtain ⟨m, rfl⟩ := hS
  rw [mul_comm]
  exact iterate_image_preperiodic_add_mul g D a b h n hn m

/-- Forward images of point closures under iterates of a finite morphism. -/
theorem iterate_image_pointClosure'
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

/-- Forward images of closures under iterates of a finite morphism. -/
theorem iterate_image_closure_eq
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] (n : ℕ) (S : Set X) :
    (f : X → X)^[n] '' closure S = closure ((f : X → X)^[n] '' S) := by
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

section Endomorphism

variable (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    (t : X ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]

/-- The weighted branch generic points of a separable map are finite. -/
theorem weightedBranchPointSet_finite_of_isGenericallySeparable
    (hsep : IsGenericallySeparable f) :
    (weightedBranchPointSet f).Finite := by
  rw [weightedBranchPointSet_eq_image_criticalPointSet]
  exact (weightedCriticalPointSet_finite_of_lift_genericallySeparable f
    (isGenericallySeparable_schemeGlobalNormalizationMorphism f hsep)).image f

include k t in
/-- The irreducible components of the weighted branch locus cover it. -/
theorem sUnion_weightedBranchLocus_components
    (hsep : IsGenericallySeparable f) :
    ⋃₀ relativeIrreducibleComponents (weightedBranchLocus f) =
      weightedBranchLocus f := by
  rw [weightedBranchLocus_components k t f hsep, Set.sUnion_image,
    ← (weightedBranchPointSet_finite_of_isGenericallySeparable f hsep).closure_biUnion,
    Set.biUnion_of_singleton]
  rfl

include k t in
/-- **Display l. 922** (`prop:pcf-equiv`, (2) ⇒ (3)). Write the actual
irreducible components of the branch locus as a finite set `T`, choose
preperiodicity data `f^{rᵢ+sᵢ}(Dᵢ) = f^{rᵢ}(Dᵢ)` with `sᵢ ≥ 1`, and put
`r = 1 + max rᵢ`, `s = lcm sᵢ`. Then `s ≥ 1` and
`f^{r+s}(crit f) = ⋃ f^{r-1+s}(Dᵢ) = ⋃ f^{r-1}(Dᵢ) = f^r(crit f)`. -/
theorem paperP_pcf_equiv_critical_orbit_chain
    (hsep : IsGenericallySeparable f)
    (T : Finset (Set X))
    (hT : (T : Set (Set X)) = relativeIrreducibleComponents (weightedBranchLocus f))
    (r s : Set X → ℕ) (hs : ∀ D ∈ T, 0 < s D)
    (hrel : ∀ D ∈ T, (f : X → X)^[r D + s D] '' D = (f : X → X)^[r D] '' D) :
    0 < T.lcm s ∧
    (f : X → X)^[(1 + T.sup r) + T.lcm s] '' weightedCriticalLocus f =
      ⋃ D ∈ T, (f : X → X)^[(1 + T.sup r) - 1 + T.lcm s] '' D ∧
    (⋃ D ∈ T, (f : X → X)^[(1 + T.sup r) - 1 + T.lcm s] '' D) =
      ⋃ D ∈ T, (f : X → X)^[(1 + T.sup r) - 1] '' D ∧
    (⋃ D ∈ T, (f : X → X)^[(1 + T.sup r) - 1] '' D) =
      (f : X → X)^[1 + T.sup r] '' weightedCriticalLocus f := by
  have hbranch : f '' weightedCriticalLocus f = ⋃ D ∈ T, D := by
    rw [← weightedBranchLocus_eq_image_criticalLocus,
      ← sUnion_weightedBranchLocus_components k t f hsep, ← hT, Set.sUnion_eq_biUnion]
    rfl
  have hshift (n : ℕ) : (f : X → X)^[n + 1] '' weightedCriticalLocus f =
      ⋃ D ∈ T, (f : X → X)^[n] '' D := by
    rw [Function.iterate_succ, Set.image_comp, hbranch, Set.image_iUnion₂]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨D, hD, h0⟩
    exact (hs D hD).ne' h0
  · rw [show 1 + T.sup r + T.lcm s = (1 + T.sup r - 1 + T.lcm s) + 1 by omega, hshift]
  · refine Set.iUnion₂_congr fun D hD => ?_
    exact iterate_image_preperiodic_of_dvd _ D (r D) (s D) (hrel D hD) _
      (by simpa using Finset.le_sup (f := r) hD) _ (Finset.dvd_lcm hD)
  · rw [show 1 + T.sup r = (1 + T.sup r - 1) + 1 by omega, hshift]
    simp

include k t in
/-- **l. 492–498** (after `def:pcf`). On the actual original variety, with
`PC(f)` the set of postcritical integral divisors (as closed point closures):
1. the union of the members of `PC(f)` is `⋃_{n ≥ 0} fⁿ(branch f)`;
2. this equals `⋃_{n ≥ 1} fⁿ(crit f)`;
3. every member of `PC(f)` is an integral divisor `closure {x}` with
   `x` of codimension one;
4. `f` carries each member of `PC(f)` to a member of `PC(f)`;
5. when `f` is PCF the union is a closed subset (the reduced divisor `PC(f)`). -/
theorem paperP_postcritical_union_identity
    (hsep : IsGenericallySeparable f) :
    ⋃₀ weightedPostcriticalComponentSet f =
        ⋃ n : ℕ, (f : X → X)^[n] '' weightedBranchLocus f ∧
    (⋃ n : ℕ, (f : X → X)^[n] '' weightedBranchLocus f) =
        ⋃ n : ℕ, (f : X → X)^[n + 1] '' weightedCriticalLocus f ∧
    (∀ D ∈ weightedPostcriticalComponentSet f,
        ∃ x : X, Order.coheight x = 1 ∧ D = closure ({x} : Set X)) ∧
    (∀ D ∈ weightedPostcriticalComponentSet f,
        (f : X → X) '' D ∈ weightedPostcriticalComponentSet f) ∧
    (IsWeightedNormalizedPCFDownstairs k t f →
        IsClosed (⋃₀ weightedPostcriticalComponentSet f)) := by
  have hfin := weightedBranchPointSet_finite_of_isGenericallySeparable f hsep
  have hmem : ∀ D, D ∈ weightedPostcriticalComponentSet f ↔
      ∃ n : ℕ, ∃ y ∈ weightedBranchPointSet f,
        D = closure ({(f : X → X)^[n] y} : Set X) := by
    intro D
    simp only [weightedPostcriticalComponentSet, weightedPostcriticalPointSet,
      Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨x, ⟨n, y, hy, rfl⟩, rfl⟩
      exact ⟨n, y, hy, rfl⟩
    · rintro ⟨n, y, hy, rfl⟩
      exact ⟨_, ⟨n, y, hy, rfl⟩, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Set.mem_sUnion, Set.mem_iUnion, hmem]
    constructor
    · rintro ⟨D, ⟨n, y, hy, rfl⟩, hz⟩
      refine ⟨n, ?_⟩
      rw [weightedBranchLocus, iterate_image_closure_eq f n]
      exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem _ hy)) hz
    · rintro ⟨n, hz⟩
      rw [weightedBranchLocus, iterate_image_closure_eq f n, ← Set.biUnion_of_singleton
        ((f : X → X)^[n] '' weightedBranchPointSet f),
        (hfin.image _).closure_biUnion] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨x, ⟨y, hy, rfl⟩, hz⟩ := hz
      exact ⟨_, ⟨n, y, hy, rfl⟩, hz⟩
  · refine Set.iUnion_congr fun n => ?_
    rw [weightedBranchLocus_eq_image_criticalLocus, Function.iterate_succ, Set.image_comp]
  · intro D hD
    obtain ⟨n, y, hy, rfl⟩ := (hmem D).mp hD
    refine ⟨_, ?_, rfl⟩
    clear hD
    induction n with
    | zero => exact weightedBranchPointSet_coheight_one k t f hy
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k t f ⟨_, ih⟩
  · intro D hD
    obtain ⟨n, y, hy, rfl⟩ := (hmem D).mp hD
    refine (hmem _).mpr ⟨n + 1, y, hy, ?_⟩
    have h := iterate_image_pointClosure' f 1 ((f : X → X)^[n] y)
    simp only [Function.iterate_one] at h
    rw [h, Function.iterate_succ_apply']
  · intro hpcf
    have hpts : (weightedPostcriticalPointSet f).Finite :=
      (isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k t f).mp hpcf
    exact (hpts.image _).isClosed_sUnion (by
      rintro D ⟨x, -, rfl⟩
      exact isClosed_closure)

end Endomorphism

/-- The union of the postcritical divisors is forward invariant. -/
theorem image_sUnion_weightedPostcriticalComponentSet_subset
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    (f : X → X) '' ⋃₀ weightedPostcriticalComponentSet f ⊆
      ⋃₀ weightedPostcriticalComponentSet f := by
  intro w hw
  obtain ⟨z, ⟨D, ⟨x, hx, rfl⟩, hz⟩, rfl⟩ := hw
  obtain ⟨n, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  refine ⟨_, ⟨_, Set.mem_iUnion.mpr ⟨n + 1, y, hy, rfl⟩, rfl⟩, ?_⟩
  have h := iterate_image_pointClosure' f 1 ((f : X → X)^[n] y)
  simp only [Function.iterate_one] at h
  change f z ∈ closure {(f : X → X)^[n + 1] y}
  rw [Function.iterate_succ_apply', ← h]
  exact ⟨z, hz, rfl⟩

/-- **Display l. 1061** (proof of `lem:covers`). For finite dominant maps
`f : X → X`, `g : Y → Y`, `π : Y → X` with `π ∘ g = f ∘ π` and `g` separable,
put `T = π(PC(g)) ∪ branch(π)` (with `PC(g)` the union of the postcritical
divisors of `g`). Then
`branch(f) ∪ f(branch π) = branch(π) ∪ π(branch g) ⊆ T`, hence
`branch(f) ⊆ T`, and `T` is forward invariant: `f(T) ⊆ T`. -/
theorem paperP_covers_branch_display
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [NoetherianSpace Y]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f) (hsep_g : IsGenericallySeparable g) :
    weightedBranchLocus f ∪ (f : X → X) '' weightedBranchLocus π =
        weightedBranchLocus π ∪ (π : Y → X) '' weightedBranchLocus g ∧
    weightedBranchLocus π ∪ (π : Y → X) '' weightedBranchLocus g ⊆
        (π : Y → X) '' ⋃₀ weightedPostcriticalComponentSet g ∪ weightedBranchLocus π ∧
    weightedBranchLocus f ⊆
        (π : Y → X) '' ⋃₀ weightedPostcriticalComponentSet g ∪ weightedBranchLocus π ∧
    (f : X → X) '' ((π : Y → X) '' ⋃₀ weightedPostcriticalComponentSet g ∪
        weightedBranchLocus π) ⊆
      (π : Y → X) '' ⋃₀ weightedPostcriticalComponentSet g ∪ weightedBranchLocus π := by
  set T := (π : Y → X) '' ⋃₀ weightedPostcriticalComponentSet g ∪ weightedBranchLocus π
  have hdisp : weightedBranchLocus f ∪ (f : X → X) '' weightedBranchLocus π =
      weightedBranchLocus π ∪ (π : Y → X) '' weightedBranchLocus g := by
    have key : ∀ (a b : Y ⟶ X) [IsFinite a] [IsDominant a] [IsFinite b] [IsDominant b],
        a = b → weightedBranchLocus a = weightedBranchLocus b := by
      intro a b _ _ _ _ h
      subst h
      rfl
    rw [← weightedBranchLocus_comp π f, ← weightedBranchLocus_comp g π]
    exact key _ _ hcomm.symm
  have hbg : weightedBranchLocus g ⊆ ⋃₀ weightedPostcriticalComponentSet g := by
    have hfin := weightedBranchPointSet_finite_of_isGenericallySeparable g hsep_g
    intro z hz
    rw [weightedBranchLocus, ← Set.biUnion_of_singleton (weightedBranchPointSet g),
      hfin.closure_biUnion] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact ⟨closure {y}, ⟨y, Set.mem_iUnion.mpr ⟨0, y, hy, rfl⟩, rfl⟩, hz⟩
  have hsub : weightedBranchLocus π ∪ (π : Y → X) '' weightedBranchLocus g ⊆ T := by
    rintro z (hz | hz)
    · exact Or.inr hz
    · exact Or.inl (Set.image_mono hbg hz)
  refine ⟨hdisp, hsub, ?_, ?_⟩
  · exact fun z hz => hsub (hdisp ▸ Or.inl hz)
  · rintro _ ⟨z, hz | hz, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := hz
      have hfw : (f : X → X) ((π : Y → X) w) = (π : Y → X) ((g : Y → Y) w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
      rw [hfw]
      exact Or.inl ⟨_, image_sUnion_weightedPostcriticalComponentSet_subset g
        ⟨w, hw, rfl⟩, rfl⟩
    · exact hsub (hdisp ▸ Or.inr ⟨z, hz, rfl⟩)

#print axioms iterate_image_preperiodic_of_dvd
#print axioms sUnion_weightedBranchLocus_components
#print axioms paperP_pcf_equiv_critical_orbit_chain
#print axioms paperP_postcritical_union_identity
#print axioms image_sUnion_weightedPostcriticalComponentSet_subset
#print axioms paperP_covers_branch_display

end

end Pcf
