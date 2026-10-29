/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module
public import Pcf.Bounding.PaperPIteration

/-! # Irreducible components of the weighted branch locus -/
@[expose] public section
namespace Pcf
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- Components of a subset, represented as maximal irreducible ambient subsets. -/
def relativeIrreducibleComponents {T : Type*} [TopologicalSpace T]
    (Z : Set T) : Set (Set T) :=
  {D | Maximal (fun C => IsIrreducible C ∧ C ⊆ Z) D}

private theorem irreducible_subtype_preimage {T : Type*} [TopologicalSpace T]
    {Z D : Set T} (hD : IsIrreducible D) (hDZ : D ⊆ Z) :
    IsIrreducible (Subtype.val ⁻¹' D : Set Z) := by
  let _ := Subtype.irreducibleSpace hD
  let g : D → Z := fun x => ⟨x.1, hDZ x.2⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have heq : g '' Set.univ = (Subtype.val ⁻¹' D : Set Z) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, Set.mem_univ _, Subtype.ext rfl⟩
  rw [← heq]
  exact (IrreducibleSpace.isIrreducible_univ D).image g hg.continuousOn

/-- The relative convention is exactly Mathlib's irreducible components
of the subspace, transported into the ambient space by subtype inclusion. -/
theorem relativeIrreducibleComponents_eq_image {T : Type*} [TopologicalSpace T]
    (Z : Set T) :
    relativeIrreducibleComponents Z =
      (fun C : Set Z => Subtype.val '' C) '' irreducibleComponents Z := by
  ext D
  constructor
  · intro hD
    refine ⟨Subtype.val ⁻¹' D, ?_, Set.image_preimage_eq_of_subset ?_⟩
    · refine ⟨irreducible_subtype_preimage hD.1.1 hD.1.2, ?_⟩
      intro C hC hDC x hx
      have hCD : Subtype.val '' C ⊆ D := hD.2
        ⟨hC.image Subtype.val continuous_subtype_val.continuousOn,
          by rintro y ⟨z, hz, rfl⟩; exact z.2⟩ (by
          intro y hy
          exact ⟨⟨y, hD.1.2 hy⟩, hDC hy, rfl⟩)
      exact hCD ⟨x, hx, rfl⟩
    · simpa only [Subtype.range_coe] using hD.1.2
  · rintro ⟨C, hC, rfl⟩
    refine ⟨⟨hC.1.image Subtype.val continuous_subtype_val.continuousOn,
      by rintro x ⟨y, hy, rfl⟩; exact y.2⟩, ?_⟩
    intro D hD hCD x hx
    have hDC : Subtype.val ⁻¹' D ⊆ C := hC.2
      (irreducible_subtype_preimage hD.1 hD.2) (by
        intro y hy
        exact hCD ⟨y, hy, rfl⟩)
    exact ⟨⟨x, hD.2 hx⟩, hDC hx, rfl⟩

private theorem finite_pointClosures_components
    {X : Scheme.{u}} (S : Set X) (hfin : S.Finite)
    (hcodim : ∀ x ∈ S, Order.coheight x = 1) :
    relativeIrreducibleComponents (closure S) =
      (fun x : X => closure ({x} : Set X)) '' S := by
  classical
  have hcover : closure S = ⋃₀ ((fun x : X => closure ({x} : Set X)) '' S) := by
    have h : closure S = ⋃ x ∈ S, closure ({x} : Set X) := by
      calc
        closure S = closure (⋃ x ∈ S, ({x} : Set X)) := by rw [Set.biUnion_of_singleton]
        _ = _ := hfin.closure_biUnion _
    rw [h]
    ext x
    simp
  have hex : ∀ D : Set X, IsIrreducible D → D ⊆ closure S →
      ∃ x ∈ S, D ⊆ closure ({x} : Set X) := by
    intro D hD hDS
    let F := hfin.image (fun x : X => closure ({x} : Set X))
    obtain ⟨C, hC, hDC⟩ := isIrreducible_iff_sUnion_isClosed.mp hD F.toFinset
      (fun C hC => by
        obtain ⟨x, hx, rfl⟩ := F.mem_toFinset.mp hC
        exact isClosed_closure)
      (by simpa only [F.coe_toFinset] using hDS.trans hcover.le)
    obtain ⟨x, hx, rfl⟩ := F.mem_toFinset.mp hC
    exact ⟨x, hx, hDC⟩
  have hanti : ∀ x ∈ S, ∀ y ∈ S,
      closure ({x} : Set X) ⊆ closure ({y} : Set X) → x = y := by
    intro x hx y hy hxy
    have hle : x ≤ y := by
      exact (show y ⤳ x from specializes_iff_mem_closure.mpr
        (hxy (subset_closure (by simp))))
    by_contra hne
    have hlt : x < y := lt_of_le_not_ge hle (fun hyx =>
      hne (Specializes.antisymm hyx hle).eq)
    have h := Order.coheight_add_one_le hlt
    rw [hcodim x hx, hcodim y hy] at h
    norm_num at h
  ext D
  constructor
  · intro hD
    obtain ⟨x, hx, hDx⟩ := hex D hD.1.1 hD.1.2
    refine ⟨x, hx, Set.Subset.antisymm ?_ hDx⟩
    exact hD.2 ⟨isIrreducible_singleton.closure,
      closure_mono (Set.singleton_subset_iff.mpr hx)⟩ hDx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨isIrreducible_singleton.closure,
      closure_mono (Set.singleton_subset_iff.mpr hx)⟩, ?_⟩
    intro D hD hxD
    obtain ⟨y, hy, hDy⟩ := hex D hD.1 hD.2
    have heq := hanti x hx y hy (hxD.trans hDy)
    simpa only [heq] using hDy

/-- Weighted branch points have codimension one on a finite-type target. -/
theorem weightedBranchPointSet_coheight_one
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    {y : Y} (hy : y ∈ weightedBranchPointSet f) : Order.coheight y = 1 := by
  obtain ⟨q, hq, rfl⟩ := hy
  exact coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k s
    (Palomar.normalizationMap Y) q

/-- `paper-p.tex`, Definition `def:crit-branch`: components are exactly the
point closures of weighted branch points, on the original target scheme. -/
theorem weightedBranchLocus_components
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparableSchemeMap f) :
    relativeIrreducibleComponents (weightedBranchLocus f) =
      (fun y : Y => closure ({y} : Set Y)) '' weightedBranchPointSet f := by
  apply finite_pointClosures_components
  · rw [weightedBranchPointSet_eq_image_criticalPointSet]
    exact (weightedCriticalPointSet_finite_of_lift_genericallySeparable f
      (isGenericallySeparable_schemeGlobalNormalizationMorphism f hsep)).image f
  · exact fun y hy => weightedBranchPointSet_coheight_one k s f hy

/-- The component correspondence using Mathlib's components of the
branch-locus subspace, transported by its inclusion into the target. -/
theorem weightedBranchLocus_subspace_components
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparableSchemeMap f) :
    (fun C : Set (weightedBranchLocus f) => Subtype.val '' C) ''
      irreducibleComponents (weightedBranchLocus f) =
        (fun y : Y => closure ({y} : Set Y)) '' weightedBranchPointSet f := by
  rw [← relativeIrreducibleComponents_eq_image]
  exact weightedBranchLocus_components k s f hsep

/-- The weighted branch points are exactly generic points of components.
The existential ranges over the actual maximal irreducible subsets. -/
theorem weightedBranchPointSet_iff_genericPoint_component
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparableSchemeMap f) (y : Y) :
    y ∈ weightedBranchPointSet f ↔
      ∃ D ∈ relativeIrreducibleComponents (weightedBranchLocus f), IsGenericPoint y D := by
  rw [weightedBranchLocus_components k s f hsep]
  constructor
  · intro hy
    exact ⟨_, ⟨y, hy, rfl⟩, isGenericPoint_closure⟩
  · rintro ⟨D, ⟨z, hz, rfl⟩, hy⟩
    have heq : y = z := (isGenericPoint_closure : IsGenericPoint z
      (closure ({z} : Set Y))).eq hy |>.symm
    exact heq ▸ hz

/-- A component is the support of the canonical reduced point-closure
subscheme at a codimension-one point. Thus the component convention agrees
with the manuscript's reduced closed-locus convention. -/
theorem weightedBranchLocus_component_reduced_representation
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparableSchemeMap f) {D : Set Y}
    (hD : D ∈ relativeIrreducibleComponents (weightedBranchLocus f)) :
    ∃ y : Y, Order.coheight y = 1 ∧
      D = Set.range (pointClosureIdealSheaf y).subschemeι ∧
      IsIntegral (pointClosureIdealSheaf y).subscheme := by
  rw [weightedBranchLocus_components k s f hsep] at hD
  obtain ⟨y, hy, rfl⟩ := hD
  refine ⟨y, weightedBranchPointSet_coheight_one k s f hy, ?_⟩
  constructor
  · rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  · exact Palomar.pointClosure_isIntegral y

section Iteration
variable (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]

omit [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)] [IsDominant f] in
private theorem iterate_image_pointClosure (n : ℕ) (x : X) :
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

include k s in
/-- `paper-p.tex`, Proposition `prop:iterates`(2), literally for components
as closed subsets on the original variety.

`paper-p.tex` correspondence: Proposition 5.3 (`prop:iterates`), item (2) of Proposition 5.3
(`item:orbit-propagation`). -/
theorem weightedBranchLocus_component_orbit_mem_pow
    (hsep : IsGenericallySeparable f) (n : ℕ) {D : Set X}
    (hD : D ∈ relativeIrreducibleComponents (weightedBranchLocus f)) :
    (f : X → X)^[n] '' D ∈ relativeIrreducibleComponents
      (weightedBranchLocus (End.of f ^ (n + 1)).asHom) := by
  rw [weightedBranchLocus_components k s f hsep] at hD
  obtain ⟨x, hx, rfl⟩ := hD
  rw [weightedBranchLocus_components k s _ (isGenericallySeparable_pow f hsep (n + 1)),
    iterate_image_pointClosure]
  exact ⟨_, weightedBranchPointSet_orbit_mem_pow f n hx, rfl⟩

/-- Postcritical integral effective divisors, represented by their closed
underlying sets; point closure gives the canonical reduced representation. -/
noncomputable def weightedPostcriticalComponentSet : Set (Set X) :=
  (fun x : X => closure ({x} : Set X)) '' weightedPostcriticalPointSet f

include k s in
/-- The postcritical component set is the union of the forward images of
actual branch components, as in `paper-p.tex`, Definition `def:pcf`.

`paper-p.tex` correspondence: Definition 3.1 (`def:pcf`), Proposition 5.3 (`prop:iterates`). -/
theorem weightedPostcriticalComponentSet_eq_component_orbits
    (hsep : IsGenericallySeparable f) :
    weightedPostcriticalComponentSet f =
      ⋃ n : ℕ, (fun D : Set X => (f : X → X)^[n] '' D) ''
        relativeIrreducibleComponents (weightedBranchLocus f) := by
  rw [weightedBranchLocus_components k s f hsep]
  ext D
  simp only [weightedPostcriticalComponentSet, weightedPostcriticalPointSet,
    Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨n, y, hy, rfl⟩, rfl⟩
    exact ⟨n, _, ⟨y, hy, rfl⟩, iterate_image_pointClosure f n y⟩
  · rintro ⟨n, C, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨n, y, hy, rfl⟩, (iterate_image_pointClosure f n y).symm⟩

omit [NoetherianSpace X] in
/-- Proposition `prop:iterates`(3), equality of the postcritical component
sets on the original scheme.

`paper-p.tex` correspondence: Proposition 5.3 (`prop:iterates`), item (3) of Proposition 5.3
(`item:pc-iterate`). -/
theorem weightedPostcriticalComponentSet_pow_eq (m : ℕ) (hm : 0 < m) :
    weightedPostcriticalComponentSet (End.of f ^ m).asHom =
      weightedPostcriticalComponentSet f := by
  simp only [weightedPostcriticalComponentSet, weightedPostcriticalPointSet_pow_eq f m hm]

include k s in
/-- Proposition `prop:iterates`(3), the branch components of any iterate
belong to the original postcritical component set.

`paper-p.tex` correspondence: Proposition 5.3 (`prop:iterates`), item (3) of Proposition 5.3
(`item:pc-iterate`). -/
theorem weightedBranchLocus_components_pow_subset_postcritical
    (hsep : IsGenericallySeparable f) (m : ℕ) :
    relativeIrreducibleComponents (weightedBranchLocus (End.of f ^ m).asHom) ⊆
      weightedPostcriticalComponentSet f := by
  rw [weightedBranchLocus_components k s _ (isGenericallySeparable_pow f hsep m)]
  exact Set.image_mono (weightedBranchPointSet_pow_subset_postcritical f m)

end Iteration
#print axioms weightedBranchLocus_subspace_components
#print axioms relativeIrreducibleComponents_eq_image
#print axioms weightedBranchLocus_component_reduced_representation
#print axioms weightedPostcriticalComponentSet_eq_component_orbits
#print axioms weightedBranchPointSet_coheight_one
#print axioms weightedBranchLocus_components
#print axioms weightedBranchPointSet_iff_genericPoint_component
#print axioms weightedBranchLocus_component_orbit_mem_pow
#print axioms weightedPostcriticalComponentSet_pow_eq
#print axioms weightedBranchLocus_components_pow_subset_postcritical
end Pcf
