/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.NodalCubicParity
public import Pcf.Examples.PaperP.NodalCubicFiberSplit
public import Pcf.Examples.PaperP.BirationalAffineNormalization
public import Pcf.Examples.PaperP.AffineLociBridge
public import Pcf.Examples.PaperP.BasilicaAffinePCF
public import Pcf.Bounding.Divisors
public import Pcf.Unnormalized.SchemeTowerBranch

/-!
# The nodal cubic: absolute normalization and the table of loci

For `paper-p.tex`, Example `ex:loci-compared`, Table `tab:loci`, and
Lemma `lem:tower-unnormalized`(3) (`item:tower-reverse`), with
`N = V(y² - x²(x+1))`, `g : A¹ → N`, `t ↦ (t² - 1, t³ - t)`, and
`h : N → A¹`, `(x, y) ↦ x`:

* `absoluteNormalizationIso`: the library's absolute normalization of `N`
  is `A¹`, over `N` (`absoluteNormalizationIso_hom_comp`).
* Row "node": `g` has reduced fibre `k × k` over the node, so the node is
  not in `branch₀(g)`; its normalized lift is the identity (isomorphism), so
  the weighted branch locus of `g` is empty; and the node is in `branch₁(g)`.
* Row "`N → A¹` at `0`": the fibre `k[y]/(y²)` is not reduced, so `0` is in
  `branch₀(h)` and `branch₁(h)`; the normalized weighted branch locus of `h`
  is contained in `{-1}`, so `0` is not in it.
* The reverse tower inclusions fail: `h ∘ g = (t ↦ t² - 1)` has `0` outside
  `branch₀` and `branch₁`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.NodalCubic

open AlgebraicGeometry CategoryTheory Polynomial

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

/-! ### The absolute normalization of the nodal cubic -/

instance parametrization_faithfulSMul : FaithfulSMul (CoordinateRing k) k[X] :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (parametrization_injective k)

/-- **The absolute normalization of the nodal cubic is the affine line**:
a typed isomorphism between `Palomar.normalization N` and `Spec k[t]`.

`paper-p.tex` correspondence: Example A.5 (`ex:loci-compared`). -/
noncomputable def absoluteNormalizationIso :
    Pcf.Palomar.normalization (Spec (.of (CoordinateRing k))) ≅ Spec (.of k[X]) :=
  BirationalAffineNormalization.normalizationIsoCover (CoordinateRing k) k[X]

/-- The identification is over the nodal cubic: composed with the
parametrization `t ↦ (t² - 1, t³ - t)` it is the normalization map.

`paper-p.tex` correspondence: Example A.5 (`ex:loci-compared`). -/
@[reassoc]
theorem absoluteNormalizationIso_hom_comp :
    (absoluteNormalizationIso k).hom ≫ normalizationSchemeMap k =
      Pcf.Palomar.normalizationMap (Spec (.of (CoordinateRing k))) :=
  BirationalAffineNormalization.normalizationIsoCover_hom_comp (CoordinateRing k) k[X]

instance nodalNormalizationMap_isFinite :
    IsFinite (Pcf.Palomar.normalizationMap (Spec (.of (CoordinateRing k)))) :=
  BirationalAffineNormalization.normalizationMap_isFinite (CoordinateRing k) k[X]

instance lineNormalizationMap_isFinite :
    IsFinite (Pcf.Palomar.normalizationMap (Spec (.of k[X]))) :=
  BirationalAffineNormalization.cover_normalizationMap_isFinite k[X]

instance normalizationSchemeMap_isDominant : IsDominant (normalizationSchemeMap k) :=
  BirationalAffineNormalization.schemeMap_isDominant (CoordinateRing k) k[X]

/-- The canonical normalized lift of `g` is an isomorphism ("the lift is the
identity" in Table `tab:loci`). -/
theorem normalizationSchemeMap_canonicalLift_isIso :
    IsIso (Pcf.schemeGlobalNormalizationMorphism (normalizationSchemeMap k)) :=
  BirationalAffineNormalization.canonicalLift_isIso (CoordinateRing k) k[X]

/-- Table `tab:loci`, row "node", normalized column: the weighted branch locus
of the normalization `g` is empty. -/
theorem normalizationSchemeMap_weightedBranchLocus_empty :
    Pcf.weightedBranchLocus (normalizationSchemeMap k) = ∅ :=
  BirationalAffineNormalization.weightedBranchLocus_empty (CoordinateRing k) k[X]

/-! ### Points -/

/-- The point `t = a` of the parameter line. -/
noncomputable abbrev paramPoint (a : k) : Spec (.of k[X]) := BasilicaAffine.closedPoint k a

instance paramPoint_isMaximal (a : k) : (paramPoint k a).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (evalRingHom a) (fun b => ⟨C b, by simp⟩)

omit [CharZero k] in
theorem paramPoint_asIdeal (a : k) :
    (paramPoint k a).asIdeal = Ideal.span {X - C a} :=
  ker_evalRingHom a

omit [CharZero k] in
theorem paramPoint_height (a : k) : (paramPoint k a).asIdeal.height = 1 := by
  rw [paramPoint_asIdeal]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (X_sub_C_ne_zero a))
    (Polynomial.not_isUnit_X_sub_C a)

omit [CharZero k] in
theorem paramPoint_coheight (a : k) : Order.coheight (paramPoint k a) = 1 := by
  rw [← idealHeight_eq_coheight (.of k[X]) (paramPoint k a)]
  exact paramPoint_height k a

/-- The point `t = a` as a divisor of the parameter line. -/
noncomputable def paramDivisor (a : k) : Pcf.SchemeDivisorPoint (Spec (.of k[X])) :=
  ⟨paramPoint k a, paramPoint_coheight k a⟩

omit [CharZero k] in
theorem paramPoint_injective : Function.Injective (paramPoint k) := by
  intro a b h
  have hmem : X - C a ∈ (paramPoint k b).asIdeal := by
    rw [← h, paramPoint_asIdeal]
    exact Ideal.subset_span rfl
  change eval b (X - C a) = 0 at hmem
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hmem
  exact hmem.symm

omit [CharZero k] in
/-- A prime containing `t - a` is the point `t = a`. -/
theorem eq_paramPoint_of_mem (q : Spec (.of k[X])) (a : k)
    (h : X - C a ∈ q.asIdeal) : q = paramPoint k a := by
  apply PrimeSpectrum.ext
  symm
  apply Ideal.IsMaximal.eq_of_le (paramPoint_isMaximal k a) q.isPrime.ne_top
  rw [paramPoint_asIdeal]
  exact (Ideal.span_singleton_le_iff_mem _).mpr h

/-- The node of `N`, the image of `t = 1`. -/
noncomputable def nodePoint : Spec (.of (CoordinateRing k)) :=
  PrimeSpectrum.comap (algebraMap (CoordinateRing k) k[X]) (paramPoint k 1)

omit [CharZero k] in
theorem normalizationSchemeMap_paramPoint_one :
    normalizationSchemeMap k (paramPoint k 1) = nodePoint k := rfl

omit [CharZero k] in
theorem mem_nodePoint_iff (c : CoordinateRing k) :
    c ∈ (nodePoint k).asIdeal ↔ (parametrization k c).eval 1 = 0 := Iff.rfl

omit [CharZero k] in
theorem normalizationSchemeMap_paramPoint_neg_one :
    normalizationSchemeMap k (paramPoint k (-1)) = nodePoint k := by
  apply PrimeSpectrum.ext
  ext c
  change (parametrization k c).eval (-1) = 0 ↔ (parametrization k c).eval 1 = 0
  have h := parametrization_eval_one_eq_eval_neg_one k c
  simp only [coe_aeval_eq_eval] at h
  rw [h]

instance nodePoint_isMaximal : (nodePoint k).asIdeal.IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap (CoordinateRing k) k[X])
    (algebraMap_isIntegral_iff.mpr inferInstance) (paramPoint k 1).asIdeal

theorem nodePoint_height : (nodePoint k).asIdeal.height = 1 := by
  change ((paramPoint k 1).asIdeal.under (CoordinateRing k)).height = 1
  rw [Pcf.height_under_eq_of_finite_of_finiteType k]
  exact paramPoint_height k 1

/-- The node as an integral effective divisor (a codimension-one point) of `N`. -/
noncomputable def nodeDivisor : Pcf.SchemeDivisorPoint (Spec (.of (CoordinateRing k))) :=
  ⟨nodePoint k, by
    rw [← idealHeight_eq_coheight (.of (CoordinateRing k)) (nodePoint k)]
    exact nodePoint_height k⟩

/-! ### The normalization over the node: row "node" of Table `tab:loci` -/

omit [CharZero k] in
theorem nodeIdeal_le_nodePoint : nodeIdeal k ≤ (nodePoint k).asIdeal := by
  apply Ideal.span_le.mpr
  intro c hc
  rcases hc with rfl | rfl
  · change (parametrization k _).eval 1 = 0
    simp
  · change (parametrization k _).eval 1 = 0
    simp

/-- The pullback of the node ideal is `(t² - 1)`. -/
theorem nodePoint_map :
    (nodePoint k).asIdeal.map (algebraMap (CoordinateRing k) k[X]) =
      normalizationOriginFiberIdeal k := by
  apply le_antisymm
  · rw [normalizationOriginFiberIdeal_eq]
    apply Ideal.map_le_iff_le_comap.mpr
    intro c hc
    change parametrization k c ∈ Ideal.span {(X : k[X]) ^ 2 - 1}
    have h1 : (parametrization k c).eval 1 = 0 := hc
    have h2 : (parametrization k c).eval (-1) = 0 := by
      have h := parametrization_eval_one_eq_eval_neg_one k c
      simp only [coe_aeval_eq_eval] at h
      rw [← h]
      exact h1
    have hd1 : X - C 1 ∣ parametrization k c := dvd_iff_isRoot.mpr h1
    have hd2 : X - C (-1) ∣ parametrization k c := dvd_iff_isRoot.mpr h2
    have hcop : IsCoprime (X - C (1 : k)) (X - C (-1)) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (by norm_num))
    have hprod := hcop.mul_dvd hd1 hd2
    have hfac : (X - C (1 : k)) * (X - C (-1)) = X ^ 2 - 1 := by
      simp only [map_neg, map_one]
      ring
    rw [hfac] at hprod
    exact Ideal.mem_span_singleton.mpr hprod
  · rw [← nodeIdeal_map]
    exact Ideal.map_mono (nodeIdeal_le_nodePoint k)

/-- Table `tab:loci`, row "node", first column: the fibre ring of `g` over the
node is `k × k`. -/
noncomputable def nodeFiberEquivProd :
    (nodePoint k).asIdeal.Fiber k[X] ≃+* k × k :=
  (AffineLociBridge.fiberRingEquivQuotient (CoordinateRing k) k[X]
    (nodePoint k).asIdeal).trans
    ((Ideal.quotEquivOfEq (nodePoint_map k)).trans (normalizationOriginFiberEquivProd k))

/-- Table `tab:loci`, row "node", first column: the node is not in `branch₀(g)`. -/
theorem nodeDivisor_not_mem_branchZero :
    nodeDivisor k ∉ Pcf.schemeUnnormalizedBranchZero (normalizationSchemeMap k) := by
  haveI : (AffineLociBridge.divisorPrime (CoordinateRing k) (nodeDivisor k)).asIdeal.IsMaximal :=
    nodePoint_isMaximal k
  change nodeDivisor k ∉ Pcf.schemeUnnormalizedBranchZero
    (AffineLociBridge.specMap (CoordinateRing k) k[X])
  rw [AffineLociBridge.mem_branchZero_iff_quotient, not_not]
  change IsReduced (k[X] ⧸ (nodePoint k).asIdeal.map (algebraMap (CoordinateRing k) k[X]))
  rw [nodePoint_map]
  exact normalizationOriginFiber_isReduced k

/-- The parametrization is not an étale ring map. -/
theorem parametrization_not_algebraEtale : ¬ Algebra.Etale (CoordinateRing k) k[X] := by
  intro h
  apply parametrization_not_flat k
  change (algebraMap (CoordinateRing k) k[X]).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- Above the node, the parametrization fails to be étale at `t = 1` or
`t = -1`; away from the node it is a localization, hence étale. -/
theorem exists_not_isEtaleAt_over_node :
    ∃ q : PrimeSpectrum k[X], PrimeSpectrum.comap (algebraMap (CoordinateRing k) k[X]) q =
      nodePoint k ∧ ¬ Algebra.IsEtaleAt (CoordinateRing k) q.asIdeal := by
  let x : CoordinateRing k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0)
  haveI : Algebra.FinitePresentation (CoordinateRing k) k[X] :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  have hloc : IsLocalization.Away x (Localization.Away (algebraMap (CoordinateRing k) k[X] x)) :=
    AffineLociBridge.isLocalization_away_of_awayMap_bijective (CoordinateRing k) k[X] x
      ⟨parametrization_away_x_injective k, parametrization_away_x_surjective k⟩
  have hD : ↑(PrimeSpectrum.basicOpen (algebraMap (CoordinateRing k) k[X] x)) ⊆
      Algebra.etaleLocus (CoordinateRing k) k[X] :=
    Algebra.basicOpen_subset_etaleLocus_iff.mpr
      (Algebra.FormallyEtale.of_isLocalization (Submonoid.powers x))
  have hne : Algebra.etaleLocus (CoordinateRing k) k[X] ≠ Set.univ := by
    rw [Ne, Algebra.etaleLocus_eq_univ_iff_etale]
    exact parametrization_not_algebraEtale k
  obtain ⟨q, hq⟩ : ∃ q, q ∉ Algebra.etaleLocus (CoordinateRing k) k[X] := by
    by_contra hall
    push Not at hall
    exact hne (Set.eq_univ_of_forall hall)
  have hxq : algebraMap (CoordinateRing k) k[X] x ∈ q.asIdeal := by
    by_contra hx
    exact hq (hD hx)
  have hx : algebraMap (CoordinateRing k) k[X] x = (X - C 1) * (X - C (-1)) := by
    rw [algebraMap_parametrization]
    simp only [x, parametrization_x, map_neg, map_one]
    ring
  rw [hx] at hxq
  refine ⟨q, ?_, hq⟩
  rcases q.isPrime.mem_or_mem hxq with h1 | h2
  · rw [eq_paramPoint_of_mem k q 1 h1]
    rfl
  · rw [eq_paramPoint_of_mem k q (-1) h2]
    exact normalizationSchemeMap_paramPoint_neg_one k

/-- Table `tab:loci`, row "node", last column: the node is in `branch₁(g)`;
`g` is not flat (hence not étale) over the node. -/
theorem nodeDivisor_mem_branchOne :
    nodeDivisor k ∈ Pcf.schemeUnnormalizedBranchOne (normalizationSchemeMap k) := by
  change nodeDivisor k ∈ Pcf.schemeUnnormalizedBranchOne
    (AffineLociBridge.specMap (CoordinateRing k) k[X])
  rw [AffineLociBridge.mem_branchOne_iff]
  exact exists_not_isEtaleAt_over_node k

/-! ### The projection `h : N → A¹`: row "`N → A¹` at `0`" -/

section Projection

/-- The `k[x]`-algebra structure of the nodal coordinate ring given by `h`. -/
@[reducible] noncomputable def projectionAlgebra : Algebra k[X] (CoordinateRing k) :=
  (projection k).toRingHom.toAlgebra

attribute [local instance] projectionAlgebra

omit [CharZero k] in
/-- `N` is generated over `k[x]` by `1` and `y`, so `h` is finite. -/
instance projection_moduleFinite : Module.Finite k[X] (CoordinateRing k) := by
  classical
  let y : CoordinateRing k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X 1)
  refine ⟨⟨{1, y}, ?_⟩⟩
  rw [eq_top_iff]
  intro c _
  obtain ⟨a, b, hc⟩ := coordinate_normalForm k c
  rw [hc]
  apply Submodule.add_mem
  · have : projection k a = a • (1 : CoordinateRing k) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · have : projection k b * y = b • y := by
      rw [Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

omit [CharZero k] in
instance projectionSchemeMap_isFinite : IsFinite (projectionSchemeMap k) := by
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (projection k).toRingHom)).mpr
  change (algebraMap k[X] (CoordinateRing k)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

omit [CharZero k] in
theorem comp_eq_basilica :
    normalizationSchemeMap k ≫ projectionSchemeMap k = BasilicaAffine.schemeMap k :=
  normalizationSchemeMap_comp_projectionSchemeMap k

instance projectionSchemeMap_isDominant : IsDominant (projectionSchemeMap k) := by
  haveI : IsDominant (normalizationSchemeMap k ≫ projectionSchemeMap k) := by
    rw [comp_eq_basilica]
    haveI := BasilicaAffine.schemeMap_surjective k
    infer_instance
  exact IsDominant.of_comp (normalizationSchemeMap k) (projectionSchemeMap k)

omit [CharZero k] in
/-- `h` sends the node to `0`. -/
theorem projectionSchemeMap_nodePoint :
    projectionSchemeMap k (nodePoint k) = paramPoint k 0 := by
  apply PrimeSpectrum.ext
  ext a
  change (parametrization k (projection k a)).eval 1 = 0 ↔ a.eval 0 = 0
  rw [parametrization_projection_apply, eval_comp]
  simp

/-- The point `0` of the target line, as a divisor. -/
noncomputable abbrev zeroDivisor : Pcf.SchemeDivisorPoint (Spec (.of k[X])) := paramDivisor k 0

omit [CharZero k] in
theorem paramPoint_zero_map_projection :
    (paramPoint k 0).asIdeal.map (algebraMap k[X] (CoordinateRing k)) =
      (Ideal.span {MvPolynomial.X 0} : Ideal (Plane k)).map (Ideal.Quotient.mk (ideal k)) := by
  rw [paramPoint_asIdeal, Ideal.map_span, Ideal.map_span]
  congr 1
  simp only [map_zero, sub_zero, Set.image_singleton]
  change {projection k X} = _
  rw [projection_X]

/-- Table `tab:loci`, row "`N → A¹`", first column: the fibre of `h` over `0`
is `k[y]/(y²)`, not reduced, so `0 ∈ branch₀(h)`. -/
theorem zeroDivisor_mem_branchZero :
    zeroDivisor k ∈ Pcf.schemeUnnormalizedBranchZero (projectionSchemeMap k) := by
  haveI : (AffineLociBridge.divisorPrime k[X] (zeroDivisor k)).asIdeal.IsMaximal :=
    paramPoint_isMaximal k 0
  change zeroDivisor k ∈ Pcf.schemeUnnormalizedBranchZero
    (AffineLociBridge.specMap k[X] (CoordinateRing k))
  rw [AffineLociBridge.mem_branchZero_iff_quotient]
  change ¬ IsReduced (CoordinateRing k ⧸
    (paramPoint k 0).asIdeal.map (algebraMap k[X] (CoordinateRing k)))
  rw [paramPoint_zero_map_projection]
  exact projectionOriginFiber_not_isReduced k

instance paramPoint_residueField_charZero (a : k) :
    CharZero (paramPoint k a).asIdeal.ResidueField :=
  charZero_of_injective_ringHom
    (f := (algebraMap k[X] (paramPoint k a).asIdeal.ResidueField).comp C)
    (RingHom.injective _)

/-- Table `tab:loci`, row "`N → A¹`", last column: `0 ∈ branch₁(h)`. -/
theorem zeroDivisor_mem_branchOne :
    zeroDivisor k ∈ Pcf.schemeUnnormalizedBranchOne (projectionSchemeMap k) := by
  haveI : CharZero (AffineLociBridge.divisorPrime k[X] (zeroDivisor k)).asIdeal.ResidueField :=
    paramPoint_residueField_charZero k 0
  exact AffineLociBridge.mem_branchOne_of_mem_branchZero k[X] (CoordinateRing k)
    (zeroDivisor k) (zeroDivisor_mem_branchZero k)

/-- The normalized weighted branch locus of `h` lies in that of `h ∘ g`, the map
`t ↦ t² - 1`, which is `{-1}`. -/
theorem projection_weightedBranchPointSet_subset :
    Pcf.weightedBranchPointSet (projectionSchemeMap k) ⊆ {paramPoint k (-1)} := by
  have hcomp := Pcf.weightedBranchPointSet_comp (normalizationSchemeMap k)
    (projectionSchemeMap k)
  have hbas : ∀ (φ : Spec (.of k[X]) ⟶ Spec (.of k[X])) [IsFinite φ] [IsDominant φ],
      φ = BasilicaAffine.schemeMap k →
        Pcf.weightedBranchPointSet φ = {BasilicaAffine.closedPoint k (-1)} := by
    rintro φ _ _ rfl
    exact BasilicaAffine.weightedBranchPointSet_eq_minusOne k
  rw [hbas _ (comp_eq_basilica k)] at hcomp
  rw [hcomp]
  exact Set.subset_union_left

/-- Table `tab:loci`, row "`N → A¹`", normalized column: `0` is not in the
weighted branch locus of `h` (the lift `t ↦ t² - 1` has reduced fibre
`k × k` over `0`). -/
theorem zero_not_mem_projection_weightedBranchLocus :
    paramPoint k 0 ∉ Pcf.weightedBranchLocus (projectionSchemeMap k) := by
  intro h0
  have hsub : Pcf.weightedBranchLocus (projectionSchemeMap k) ⊆ {paramPoint k (-1)} := by
    unfold Pcf.weightedBranchLocus
    rw [← (BasilicaAffine.closedPoint_isClosed k (-1)).closure_eq]
    exact closure_mono (projection_weightedBranchPointSet_subset k)
  have := paramPoint_injective k (hsub h0)
  norm_num at this

end Projection

#print axioms absoluteNormalizationIso
#print axioms absoluteNormalizationIso_hom_comp
#print axioms normalizationSchemeMap_canonicalLift_isIso
#print axioms normalizationSchemeMap_weightedBranchLocus_empty
#print axioms nodeDivisor
#print axioms nodeFiberEquivProd
#print axioms nodeDivisor_not_mem_branchZero
#print axioms exists_not_isEtaleAt_over_node
#print axioms nodeDivisor_mem_branchOne
#print axioms projectionSchemeMap_isFinite
#print axioms projectionSchemeMap_isDominant
#print axioms projectionSchemeMap_nodePoint
#print axioms zeroDivisor_mem_branchZero
#print axioms zeroDivisor_mem_branchOne
#print axioms projection_weightedBranchPointSet_subset
#print axioms zero_not_mem_projection_weightedBranchLocus

end Pcf.Examples.PaperP.NodalCubic
