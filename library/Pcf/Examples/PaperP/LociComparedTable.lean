/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.NodalCubicLoci
public import Pcf.Examples.PaperP.CuspCanonicalLift

/-!
# Table `tab:loci` and the reverse tower containments

For `paper-p.tex`, Example `ex:loci-compared` and Table `tab:loci`, this file
completes the three rows of the table for the actual affine scheme maps, and
proves Lemma `lem:tower-unnormalized`(3) (`item:tower-reverse`): the reverse
inclusions of `branch₀(h ∘ g) ⊆ branch₀(h) ∪ h(branch₀(g))` and
`branch₁(h ∘ g) ⊆ branch₁(h) ∪ h(branch₁(g))` fail for the nodal
normalization `g` and the projection `h`.

Row "cusp" (map `u ↦ (u², u³)` onto `V(y² - x³)`, at the cusp):
`cuspDivisor_mem_branchZero`, `cuspDivisor_mem_branchOne`,
and `cusp_weightedBranchLocus_empty`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Pcf.Examples.PaperP.NodalCubic

universe u

variable (k : Type u) [Field k] [CharZero k]

/-! ### The composite `h ∘ g = (t ↦ t² - 1)` -/

theorem basilica_zero_map :
    (paramPoint k 0).asIdeal.map (BasilicaAffine.coordinateMap k).toRingHom =
      normalizationOriginFiberIdeal k := by
  rw [paramPoint_asIdeal, Ideal.map_span, normalizationOriginFiberIdeal_eq]
  congr 1
  simp only [map_zero, sub_zero, Set.image_singleton]
  change {BasilicaAffine.coordinateMap k X} = _
  rw [BasilicaAffine.coordinateMap_X]

/-- The composite `h ∘ g` has reduced fibre over `0`, so `0 ∉ branch₀(h ∘ g)`. -/
theorem zeroDivisor_not_mem_comp_branchZero :
    zeroDivisor k ∉ Pcf.schemeUnnormalizedBranchZero
      (normalizationSchemeMap k ≫ projectionSchemeMap k) := by
  rw [comp_eq_basilica]
  letI alg : Algebra k[X] k[X] := (BasilicaAffine.coordinateMap k).toRingHom.toAlgebra
  haveI hmax : (AffineLociBridge.divisorPrime k[X] (zeroDivisor k)).asIdeal.IsMaximal :=
    paramPoint_isMaximal k 0
  have h := @AffineLociBridge.mem_branchZero_iff_quotient k[X] k[X] _ _ alg (zeroDivisor k) hmax
  change zeroDivisor k ∉ Pcf.schemeUnnormalizedBranchZero
    (Spec.map (CommRingCat.ofHom (@algebraMap k[X] k[X] _ _ alg)))
  rw [h, not_not]
  have hI : (AffineLociBridge.divisorPrime k[X] (zeroDivisor k)).asIdeal.map
      (@algebraMap k[X] k[X] _ _ alg) = normalizationOriginFiberIdeal k :=
    basilica_zero_map k
  rw [hI]
  exact normalizationOriginFiber_isReduced k

/-- The composite `h ∘ g` is étale above `0`, so `0 ∉ branch₁(h ∘ g)`. -/
theorem zeroDivisor_not_mem_comp_branchOne :
    zeroDivisor k ∉ Pcf.schemeUnnormalizedBranchOne
      (normalizationSchemeMap k ≫ projectionSchemeMap k) := by
  rw [comp_eq_basilica]
  rintro ⟨x, hx, hnot⟩
  apply hnot
  apply AffineLociBridge.stalk_formallyEtale_of_isStacksEtaleAt
  apply BasilicaAffine.etaleAt_of_ne_zero
  intro hx0
  rw [hx0, BasilicaAffine.zero_to_minusOne] at hx
  have := paramPoint_injective k hx
  norm_num at this

/-! ### `lem:tower-unnormalized`(3): the reverse inclusions fail -/

/-- `item:tower-reverse` for `branch₀`: `0 ∈ branch₀(h)` but
`0 ∉ branch₀(h ∘ g)`.

`paper-p.tex` correspondence: item (3) of Lemma A.6 (`item:tower-reverse`). -/
theorem tower_reverse_branchZero_fails :
    ¬ (Pcf.schemeUnnormalizedBranchZero (projectionSchemeMap k) ∪
        Pcf.schemeDivisorPushImage (projectionSchemeMap k)
          (Pcf.schemeUnnormalizedBranchZero (normalizationSchemeMap k)) ⊆
      Pcf.schemeUnnormalizedBranchZero
        (normalizationSchemeMap k ≫ projectionSchemeMap k)) := fun hsub =>
  zeroDivisor_not_mem_comp_branchZero k (hsub (Or.inl (zeroDivisor_mem_branchZero k)))

/-- `0 ∈ h(branch₁(g))`: the node lies in `branch₁(g)` and maps to `0`. -/
theorem zeroDivisor_mem_push_branchOne :
    zeroDivisor k ∈ Pcf.schemeDivisorPushImage (projectionSchemeMap k)
      (Pcf.schemeUnnormalizedBranchOne (normalizationSchemeMap k)) :=
  ⟨nodeDivisor k, nodeDivisor_mem_branchOne k, projectionSchemeMap_nodePoint k⟩

/-- `item:tower-reverse` for `branch₁`: `0 ∈ h(branch₁(g))` (and
`0 ∈ branch₁(h)`) but `0 ∉ branch₁(h ∘ g)`.

`paper-p.tex` correspondence: item (3) of Lemma A.6 (`item:tower-reverse`). -/
theorem tower_reverse_branchOne_fails :
    ¬ (Pcf.schemeUnnormalizedBranchOne (projectionSchemeMap k) ∪
        Pcf.schemeDivisorPushImage (projectionSchemeMap k)
          (Pcf.schemeUnnormalizedBranchOne (normalizationSchemeMap k)) ⊆
      Pcf.schemeUnnormalizedBranchOne
        (normalizationSchemeMap k ≫ projectionSchemeMap k)) := fun hsub =>
  zeroDivisor_not_mem_comp_branchOne k (hsub (Or.inr (zeroDivisor_mem_push_branchOne k)))

/-- Both parts of `item:tower-reverse`, with the witnesses used in the
manuscript's proof.

`paper-p.tex` correspondence: Lemma A.6 (`lem:tower-unnormalized`), item (3) of Lemma A.6
(`item:tower-reverse`). -/
theorem tower_reverse :
    (zeroDivisor k ∈ Pcf.schemeUnnormalizedBranchZero (projectionSchemeMap k) ∧
      zeroDivisor k ∉ Pcf.schemeUnnormalizedBranchZero
        (normalizationSchemeMap k ≫ projectionSchemeMap k)) ∧
    (zeroDivisor k ∈ Pcf.schemeDivisorPushImage (projectionSchemeMap k)
        (Pcf.schemeUnnormalizedBranchOne (normalizationSchemeMap k)) ∧
      zeroDivisor k ∉ Pcf.schemeUnnormalizedBranchOne
        (normalizationSchemeMap k ≫ projectionSchemeMap k)) :=
  ⟨⟨zeroDivisor_mem_branchZero k, zeroDivisor_not_mem_comp_branchZero k⟩,
    ⟨zeroDivisor_mem_push_branchOne k, zeroDivisor_not_mem_comp_branchOne k⟩⟩

end Pcf.Examples.PaperP.NodalCubic

namespace Pcf.Examples.PaperP.CuspOriginalFibre

universe u

variable (k : Type u) [Field k] [CharZero k]

/-! ### Row "cusp" of Table `tab:loci` -/

/-- The `k[x,y]/(y²-x³)`-algebra structure of `k[u]` given by the parametrization. -/
@[reducible] noncomputable def cuspAlgebra : Algebra (CoordinateRing k) k[X] :=
  (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra

attribute [local instance] cuspAlgebra

instance cusp_moduleFinite : Module.Finite (CoordinateRing k) k[X] := cuspParam_finite k

instance cusp_faithfulSMul : FaithfulSMul (CoordinateRing k) k[X] :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (cuspParam_injective k)

/-- The cusp point, the image of `u = 0`. -/
noncomputable def cuspPoint : Spec (.of (CoordinateRing k)) :=
  PrimeSpectrum.comap (algebraMap (CoordinateRing k) k[X]) (NodalCubic.paramPoint k 0)

theorem cuspPoint_asIdeal : (cuspPoint k).asIdeal = originIdeal k := by
  symm
  apply Ideal.IsMaximal.eq_of_le (originIdeal_isMaximal k) (cuspPoint k).isPrime.ne_top
  unfold originIdeal
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro a ha
  rcases ha with rfl | rfl
  · change ((Pcf.Examples.Cusp.cuspParam k) (Ideal.Quotient.mk _ _)).eval 0 = 0
    simp [Pcf.Examples.Cusp.cuspParam]
  · change ((Pcf.Examples.Cusp.cuspParam k) (Ideal.Quotient.mk _ _)).eval 0 = 0
    simp [Pcf.Examples.Cusp.cuspParam]

instance cuspPoint_isMaximal : (cuspPoint k).asIdeal.IsMaximal := by
  rw [cuspPoint_asIdeal]
  exact originIdeal_isMaximal k

/-- The cusp as an integral effective divisor of the cuspidal cubic. -/
noncomputable def cuspDivisor : Pcf.SchemeDivisorPoint (Spec (.of (CoordinateRing k))) :=
  ⟨cuspPoint k, by
    rw [← idealHeight_eq_coheight (.of (CoordinateRing k)) (cuspPoint k)]
    change ((NodalCubic.paramPoint k 0).asIdeal.under (CoordinateRing k)).height = 1
    rw [Pcf.height_under_eq_of_finite_of_finiteType k]
    exact NodalCubic.paramPoint_height k 0⟩

/-- Table `tab:loci`, row "cusp", first column: the fibre over the cusp is
`k[u]/(u²)`, not reduced, so the cusp is in `branch₀`. -/
theorem cuspDivisor_mem_branchZero :
    cuspDivisor k ∈ Pcf.schemeUnnormalizedBranchZero (schemeMap k) := by
  haveI : (AffineLociBridge.divisorPrime (CoordinateRing k) (cuspDivisor k)).asIdeal.IsMaximal :=
    cuspPoint_isMaximal k
  change cuspDivisor k ∈ Pcf.schemeUnnormalizedBranchZero
    (AffineLociBridge.specMap (CoordinateRing k) k[X])
  rw [AffineLociBridge.mem_branchZero_iff_quotient]
  change ¬ IsReduced (k[X] ⧸ (cuspPoint k).asIdeal.map (algebraMap (CoordinateRing k) k[X]))
  rw [cuspPoint_asIdeal]
  exact originFiber_not_isReduced k

instance cuspPoint_residueField_charZero : CharZero (cuspPoint k).asIdeal.ResidueField :=
  charZero_of_injective_ringHom
    (f := (algebraMap (CoordinateRing k) (cuspPoint k).asIdeal.ResidueField).comp
      (algebraMap k (CoordinateRing k)))
    (RingHom.injective _)

/-- Table `tab:loci`, row "cusp", last column: the cusp is in `branch₁`. -/
theorem cuspDivisor_mem_branchOne :
    cuspDivisor k ∈ Pcf.schemeUnnormalizedBranchOne (schemeMap k) := by
  haveI : CharZero (AffineLociBridge.divisorPrime (CoordinateRing k)
      (cuspDivisor k)).asIdeal.ResidueField := cuspPoint_residueField_charZero k
  exact AffineLociBridge.mem_branchOne_of_mem_branchZero (CoordinateRing k) k[X]
    (cuspDivisor k) (cuspDivisor_mem_branchZero k)

end Pcf.Examples.PaperP.CuspOriginalFibre

namespace Pcf.Examples.PaperP.LociComparedTable

open Pcf.Examples.PaperP

universe u

variable (k : Type u) [Field k] [CharZero k]

attribute [local instance] CuspOriginalFibre.schemeMap_isFinite
  CuspOriginalFibre.cuspSchemeMap_isDominant

local instance cuspNormalizationFinite :
    IsFinite (Pcf.Palomar.normalizationMap
      (Spec (.of (CuspOriginalFibre.CoordinateRing k)))) := by
  rw [← CuspOriginalFibre.cuspNormalizationToParameterLine_comp k]
  letI : IsIso (CuspOriginalFibre.cuspNormalizationToParameterLine k) :=
    CuspOriginalFibre.cuspNormalizationToParameterLine_isIso k
  infer_instance

/-- **Table `tab:loci`**, all nine entries, for the actual affine scheme maps.

Row 1 (`u ↦ (u², u³)`, at the cusp): in `branch₀`, normalized weighted branch
locus empty (the lift is an isomorphism), in `branch₁`.
Row 2 (`t ↦ (t² - 1, t³ - t)`, at the node): not in `branch₀` (fibre `k × k`),
normalized weighted branch locus empty, in `branch₁` (not flat).
Row 3 (`N → A¹`, at `0`): in `branch₀` (fibre `k[y]/(y²)`), not in the
normalized weighted branch locus, in `branch₁`.

`paper-p.tex` correspondence: Example A.5 (`ex:loci-compared`), Table 1 (`tab:loci`). -/
theorem table_loci :
    (CuspOriginalFibre.cuspDivisor k ∈
        Pcf.schemeUnnormalizedBranchZero (CuspOriginalFibre.schemeMap k) ∧
      Pcf.weightedBranchLocus (CuspOriginalFibre.schemeMap k) = ∅ ∧
      CuspOriginalFibre.cuspDivisor k ∈
        Pcf.schemeUnnormalizedBranchOne (CuspOriginalFibre.schemeMap k)) ∧
    (NodalCubic.nodeDivisor k ∉
        Pcf.schemeUnnormalizedBranchZero (NodalCubic.normalizationSchemeMap k) ∧
      Pcf.weightedBranchLocus (NodalCubic.normalizationSchemeMap k) = ∅ ∧
      NodalCubic.nodeDivisor k ∈
        Pcf.schemeUnnormalizedBranchOne (NodalCubic.normalizationSchemeMap k)) ∧
    (NodalCubic.zeroDivisor k ∈
        Pcf.schemeUnnormalizedBranchZero (NodalCubic.projectionSchemeMap k) ∧
      NodalCubic.paramPoint k 0 ∉
        Pcf.weightedBranchLocus (NodalCubic.projectionSchemeMap k) ∧
      NodalCubic.zeroDivisor k ∈
        Pcf.schemeUnnormalizedBranchOne (NodalCubic.projectionSchemeMap k)) :=
  ⟨⟨CuspOriginalFibre.cuspDivisor_mem_branchZero k,
      CuspOriginalFibre.cusp_weightedBranchLocus_empty k,
      CuspOriginalFibre.cuspDivisor_mem_branchOne k⟩,
    ⟨NodalCubic.nodeDivisor_not_mem_branchZero k,
      NodalCubic.normalizationSchemeMap_weightedBranchLocus_empty k,
      NodalCubic.nodeDivisor_mem_branchOne k⟩,
    ⟨NodalCubic.zeroDivisor_mem_branchZero k,
      NodalCubic.zero_not_mem_projection_weightedBranchLocus k,
      NodalCubic.zeroDivisor_mem_branchOne k⟩⟩

end Pcf.Examples.PaperP.LociComparedTable

#print axioms Pcf.Examples.PaperP.NodalCubic.zeroDivisor_not_mem_comp_branchZero
#print axioms Pcf.Examples.PaperP.NodalCubic.zeroDivisor_not_mem_comp_branchOne
#print axioms Pcf.Examples.PaperP.NodalCubic.tower_reverse_branchZero_fails
#print axioms Pcf.Examples.PaperP.NodalCubic.tower_reverse_branchOne_fails
#print axioms Pcf.Examples.PaperP.NodalCubic.tower_reverse
#print axioms Pcf.Examples.PaperP.CuspOriginalFibre.cuspDivisor_mem_branchZero
#print axioms Pcf.Examples.PaperP.CuspOriginalFibre.cuspDivisor_mem_branchOne
#print axioms Pcf.Examples.PaperP.LociComparedTable.table_loci
