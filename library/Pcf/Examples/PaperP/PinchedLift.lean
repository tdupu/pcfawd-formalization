/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNodeFibre
public import Pcf.Examples.PaperP.QuadricConeSquaringEtale

/-!
# The lift `z ↦ z²` of `g` is `0`-PCF and `1`-PCF

For `paper-p.tex`, Remark `rem:pinched-unnormalized` ("the lift `z ↦ z²` of `g` is
`0`-PCF and `1`-PCF, and `g` is neither"), with `ν_B : 𝔸¹_z → B` the normalization of
the nodal line `B = Spec R_B`:

* `liftMap_comp_nuB : z² ∘ ν_B = ν_B ∘ ... ` i.e. `liftMap ≫ ν_B = ν_B ≫ g`: the squaring
  map of `𝔸¹` lifts `g` (`g* p = p(z²)`).
* `branchOne_subset`: the unnormalized `branch₁` of `z ↦ z²` is contained in `{0}`
  (squaring is étale where `z` is invertible); `branchZero_subset` likewise.
* `lift_isSchemeUnnormalizedPCF i`: the lift is `i`-PCF for `i = 0, 1`; with
  `PinchedNodeFibre.not_isSchemeUnnormalizedPCF`, this is the remark's failure of
  descent from the normalization for the unnormalized loci.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedLift

open AlgebraicGeometry CategoryTheory Polynomial

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The lift `z ↦ z²` on `𝔸¹_z`. -/
noncomputable abbrev liftMap : Spec (.of k[X]) ⟶ Spec (.of k[X]) :=
  QuadricConeRestriction.schemeMap k

instance liftMap_isFinite : IsFinite (liftMap k) := QuadricConeRestriction.schemeMap_finite k
instance liftMap_surjective : Surjective (liftMap k) :=
  QuadricConeRestriction.schemeMap_surjective k
instance liftMap_isDominant : IsDominant (liftMap k) := inferInstance

/-- The normalization `ν_B : 𝔸¹_z → B`. -/
noncomputable def nuB : Spec (.of k[X]) ⟶ Spec (.of (PinchedNodeFibre.NodeRing k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PinchedNodeFibre.NodeRing k) k[X]))

omit [CharZero k] in
/-- **`z ↦ z²` lifts `g`**: `liftMap ≫ ν_B = ν_B ≫ g`. -/
theorem liftMap_comp_nuB : liftMap k ≫ nuB k = nuB k ≫ PinchedNodeFibre.gScheme k := by
  unfold liftMap QuadricConeRestriction.schemeMap nuB PinchedNodeFibre.gScheme
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The structure map `𝔸¹ → Spec k`. -/
noncomputable def structureMap : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k[X]))

instance structureMap_locallyOfFiniteType : LocallyOfFiniteType (structureMap k) := by
  unfold structureMap
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The origin `z = 0` as a divisor of `𝔸¹`. -/
noncomputable abbrev originDivisor : Pcf.SchemeDivisorPoint (Spec (.of k[X])) :=
  NodalCubic.paramDivisor k 0

theorem liftMap_origin : liftMap k (NodalCubic.paramPoint k 0) = NodalCubic.paramPoint k 0 := by
  apply NodalCubic.eq_paramPoint_of_mem
  change Polynomial.expand k 2 (X - C 0) ∈ (NodalCubic.paramPoint k 0).asIdeal
  rw [NodalCubic.paramPoint_asIdeal, map_zero, sub_zero, expand_X, Ideal.mem_span_singleton]
  simp

/-- **`branch₁(z ↦ z²) ⊆ {0}`**. -/
theorem branchOne_subset :
    Pcf.schemeUnnormalizedBranchOne (liftMap k) ⊆ {originDivisor k} := by
  rintro E ⟨x, hx, hnot⟩
  have hX : (X : k[X]) ∈ x.asIdeal := by
    by_contra hX
    exact hnot (AffineLociBridge.stalk_formallyEtale_of_isStacksEtaleAt _ x
      (QuadricConeRestriction.schemeMap_isStacksEtaleAt_of_X_notMem k x hX))
  have hx0 : x = NodalCubic.paramPoint k 0 :=
    NodalCubic.eq_paramPoint_of_mem k x 0 (by simpa using hX)
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  rw [← hx, hx0, liftMap_origin]
  rfl

instance residueField_charZero (P : Spec (.of k[X])) : CharZero P.asIdeal.ResidueField :=
  charZero_of_injective_ringHom
    (f := (algebraMap k[X] P.asIdeal.ResidueField).comp (algebraMap k k[X]))
    (RingHom.injective _)

/-- `branch₀(z ↦ z²) ⊆ branch₁(z ↦ z²)` (finite map, characteristic zero). -/
theorem branchZero_subset_branchOne :
    Pcf.schemeUnnormalizedBranchZero (liftMap k) ⊆ Pcf.schemeUnnormalizedBranchOne (liftMap k) := by
  intro E hE
  letI alg : Algebra k[X] k[X] := (QuadricConeRestriction.coordinateMap k).toRingHom.toAlgebra
  haveI hfin : @Module.Finite k[X] k[X] _ _ alg.toModule :=
    QuadricConeRestriction.coordinateMap_finite k
  exact @AffineLociBridge.mem_branchOne_of_mem_branchZero k[X] k[X] _ _ alg hfin E
    (residueField_charZero k E.1) hE

/-- **`branch_i(z ↦ z²) ⊆ {0}`** for `i = 0, 1`. -/
theorem branch_subset (i : Bool) :
    Pcf.schemeUnnormalizedBranch i (liftMap k) ⊆ {originDivisor k} := by
  cases i
  · exact (branchZero_subset_branchOne k).trans (branchOne_subset k)
  · exact branchOne_subset k

/-- **The lift `z ↦ z²` of `g` is `0`-PCF and `1`-PCF**: its unnormalized postcritical
sets are contained in `{0}`. -/
theorem lift_postcriticalSet_subset (i : Bool) :
    Pcf.schemeUnnormalizedPostcriticalSet i k (structureMap k) (liftMap k) ⊆
      {originDivisor k} := by
  intro D hD
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hD
  obtain ⟨E, hE, rfl⟩ := hn
  have hE0 := branch_subset k i hE
  rw [Set.mem_singleton_iff] at hE0
  subst hE0
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  rw [Pcf.schemeDivisorIterateOfFiniteType_val]
  exact Pcf.end_pow_apply_eq_of_apply_eq (liftMap k) _ (liftMap_origin k) n

/-- `paper-p.tex` correspondence: Remark A.12 (`rem:pinched-unnormalized`). -/
theorem lift_isSchemeUnnormalizedPCF (i : Bool) :
    Pcf.IsSchemeUnnormalizedPCF i k (structureMap k) (liftMap k) :=
  (Set.finite_singleton _).subset (lift_postcriticalSet_subset k i)

#print axioms liftMap_comp_nuB
#print axioms branchOne_subset
#print axioms lift_isSchemeUnnormalizedPCF

end Pcf.Examples.PaperP.PinchedLift
