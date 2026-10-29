/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNodePCF
public import Pcf.Examples.PaperP.PinchedSigmaExact
public import Pcf.Examples.PaperP.PinchedNotFlat
public import Pcf.Examples.PaperP.PinchedLineScheme
public import Pcf.Unnormalized.PaperPRegularCodimOneLoci
public import Pcf.Bounding.AllCodimCoreGood

/-!
# `rem:pinched-unnormalized`, packaged

For `paper-p.tex`, Remark `rem:pinched-unnormalized`.

* `f_formallyEtale_of_codimOne`: **near `o` the map `f` is étale in codimension one**. The
  basic open `D(w z²)` of `X` contains `o` (`oPoint_mem_basicOpen`), and `f` is formally étale at
  every codimension-one point of it. Proof: in characteristic zero `X` is regular in codimension
  one, so the non-étale codimension-one points of `f` map to the weighted branch divisors
  `ν(V(z))`, `ν(V(w))` (`weightedBranchPointSet_eq_unnormalized_of_regularInCodimOne`,
  `PinchedBranchExact.weightedBranchPointSet_eq`); a point mapping to `ν(V(z))` contains
  `f*(z²) = (z²)²`, a point mapping to `ν(V(w))` contains `f*(w) = w²`.
* `pinched_unnormalized_remark`: the whole remark as one statement, assembled from
  `PinchedBranchExact`, `PinchedLine`, `PinchedLineScheme`, `PinchedNodePCF`,
  `PinchedNodeFibre`, `PinchedSigmaExact`, `PinchedBoundingFailure`, `PinchedNodeFibreLength`,
  `PinchedNotFlat` and `PinchedLift`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedUnnormalizedRemark

open AlgebraicGeometry CategoryTheory MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedAmbient
open Pcf.Examples.PaperP.PinchedBranchExact Pcf.Examples.PaperP.PinchedLocalStructure
open Pcf.Examples.PaperP.PinchedPostcritical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k

/-- `w z² ∈ R`. -/
noncomputable def abElt : R :=
  PinchedRing.mk k (X 1 * X 0 ^ 2) ((pinchedAlg k).mul_mem (w_mem k) (z_sq_mem k))

theorem abElt_eq : abElt k = PinchedSigmaExact.wElt k * bElt k := rfl

/-- `o ∈ D(w z²)`. -/
theorem oPoint_mem_basicOpen : oPoint k ∈ PrimeSpectrum.basicOpen (abElt k) := by
  change abElt k ∉ oIdeal k
  rw [mem_oIdeal_iff]
  change aeval ![(2 : k), 1] (X 1 * X 0 ^ 2) ≠ 0
  simp

/-- A codimension-one point of `X` is mapped by `f` to a codimension-one point. -/
theorem coheight_f (x : Pcf.SchemeDivisorPoint (Xs k)) : Order.coheight (fScheme k x.1) = 1 :=
  Pcf.coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k (structureMap k) (fScheme k) x

/-- **Near `o`, `f` is étale in codimension one**: `f` is formally étale at every
codimension-one point of `D(w z²) ∋ o`.

`paper-p.tex` correspondence: Remark A.12 (`rem:pinched-unnormalized`). -/
theorem f_formallyEtale_of_codimOne (x : Pcf.SchemeDivisorPoint (Xs k))
    (hx : x.1 ∈ PrimeSpectrum.basicOpen (abElt k)) :
    ((fScheme k).stalkMap x.1).hom.FormallyEtale := by
  by_contra hne
  let E : Pcf.SchemeDivisorPoint (Xs k) := ⟨fScheme k x.1, coheight_f k x⟩
  have hmem : fScheme k x.1 ∈
      {y : Xs k | ∃ E ∈ Pcf.schemeUnnormalizedBranchOne (fScheme k), E.1 = y} :=
    ⟨E, ⟨x.1, rfl, hne⟩, rfl⟩
  have hloci := Pcf.weightedBranchPointSet_eq_unnormalized_of_regularInCodimOne (fScheme k) k
    (structureMap k) (structureMap k) (stalk_isRegularLocalRing k) (stalk_isRegularLocalRing k)
  rw [← hloci.2, ← hloci.1, weightedBranchPointSet_eq] at hmem
  obtain ⟨i, hi⟩ := hmem
  apply hx
  change abElt k ∈ x.1.asIdeal
  rw [abElt_eq]
  fin_cases i
  · -- `f x = ν(V(z))`: `f*(z²) = (z²)² ∈ x`
    have h : bElt k ∈ (fScheme k x.1).asIdeal := hi ▸ PinchedSigmaExact.bElt_mem_axis_zero k
    change fStar k (bElt k) ∈ x.1.asIdeal at h
    have hsq : fStar k (bElt k) = bElt k ^ 2 := by
      apply Subtype.ext
      change squaringMap k (X 0 ^ 2) = (X 0 ^ 2) ^ 2
      simp [squaringMap]
    rw [hsq] at h
    exact Ideal.mul_mem_left _ _ (x.1.isPrime.mem_of_pow_mem 2 h)
  · -- `f x = ν(V(w))`: `f*(w) = w² ∈ x`
    have h : PinchedSigmaExact.wElt k ∈ (fScheme k x.1).asIdeal :=
      hi ▸ PinchedSigmaExact.wElt_mem_axis_one k
    change fStar k (PinchedSigmaExact.wElt k) ∈ x.1.asIdeal at h
    have hsq : fStar k (PinchedSigmaExact.wElt k) = PinchedSigmaExact.wElt k ^ 2 := by
      apply Subtype.ext
      change squaringMap k (X 1) = X 1 ^ 2
      simp [squaringMap]
    rw [hsq] at h
    exact Ideal.mul_mem_right _ _ (x.1.isPrime.mem_of_pow_mem 2 h)

/-- `Q = ν(4, 1)` is not `ν(0, 1)`. -/
theorem pointInX_four_ne_zero :
    PinchedBoundingFailure.pointInX k 4 ≠ PinchedBoundingFailure.pointInX k 0 := by
  intro h
  have h0 : bElt k ∈ (PinchedBoundingFailure.pointInX k 0).asIdeal := by
    rw [PinchedSigma.mem_pointInX_iff]
    change aeval ![(0 : k), 1] (X 0 ^ 2) = 0
    simp
  rw [← h, PinchedSigma.mem_pointInX_iff] at h0
  change aeval ![(4 : k), 1] (X 0 ^ 2) = 0 at h0
  simp at h0

/-- **`Q ∉ Σ = {ν(0, 1), o}`.**

`paper-p.tex` correspondence: Remark A.12 (`rem:pinched-unnormalized`). -/
theorem pointQ_not_mem_sigma : PinchedBoundingFailure.pointInX k 4 ∉ PinchedSigmaExact.Sigma k := by
  rw [PinchedSigmaExact.sigma_eq]
  rintro (h | h)
  · exact pointInX_four_ne_zero k h
  · exact PinchedBoundingFailure.pointInX_four_ne_o k h

/-- `f` is PCF in the sense of `def:pcf` (generic separability included). -/
theorem f_isSeparableNormalizedPCF :
    Pcf.IsSeparableNormalizedPCF k (structureMap k) (fScheme k) :=
  (Pcf.isSeparableNormalizedPCF_iff_downstairs k (structureMap k) _).2
    ⟨Pcf.isGenericallySeparable_of_charZero_field k (structureMap k) _, f_isPCF k⟩

/-- **Remark `rem:pinched-unnormalized`**, all its checkable claims in one statement.

1. `f` is PCF, `0`-PCF and `1`-PCF.
2. `B = ν(V(w - 1))` is an `f`-invariant integral effective divisor (its generic point is fixed and
   has height one), and the restriction of `f` to the reduced closed subscheme `B` is `g`
   (transported along `B ≅ Spec R_B`).
3. `g` is PCF but neither `0`-PCF nor `1`-PCF.
4. `Σ = {ν(0, 1), o}` and `Q = ν(4, 1) ∉ Σ`; `Q` is a regular point of `B`.
5. `o` is the only point of `B` over `Q`, and `g` is not étale at `o`.
6. Near `o`, `f` is étale in codimension one (on `D(w z²) ∋ o`) but `f` is not flat at `o`.
7. The lift `z ↦ z²` of `g` is `0`-PCF and `1`-PCF.

`paper-p.tex` correspondence: Remark 2.3 (`rem:why-normalized`), Remark A.12 (`rem:pinched-
unnormalized`). -/
theorem pinched_unnormalized_remark :
    -- (1)
    Pcf.IsSeparableNormalizedPCF k (structureMap k) (fScheme k) ∧
    Pcf.IsSchemeUnnormalizedPCF false k (structureMap k) (fScheme k) ∧
    Pcf.IsSchemeUnnormalizedPCF true k (structureMap k) (fScheme k) ∧
    -- (2)
    fScheme k (PinchedLine.bPoint k) = PinchedLine.bPoint k ∧
    (PinchedLine.bPoint k).asIdeal.height = 1 ∧
    PinchedLineScheme.gSub k =
      (PinchedLineScheme.bSubschemeIso k).hom ≫ PinchedNodeFibre.gScheme k ≫
        (PinchedLineScheme.bSubschemeIso k).inv ∧
    -- (3)
    Pcf.IsSeparableNormalizedPCF k (PinchedNodeFibre.structureMap k) (PinchedNodeFibre.gScheme k) ∧
    (∀ i : Bool, ¬ Pcf.IsSchemeUnnormalizedPCF i k (PinchedNodeFibre.structureMap k)
      (PinchedNodeFibre.gScheme k)) ∧
    -- (4)
    PinchedSigmaExact.Sigma k = {PinchedBoundingFailure.pointInX k 0, oPoint k} ∧
    PinchedBoundingFailure.pointInX k 4 ∉ PinchedSigmaExact.Sigma k ∧
    IsRegularLocalRing (Localization.AtPrime (PinchedNodeFibre.pointQ k 4).asIdeal) ∧
    -- (5)
    PinchedBoundingFailure.pointInX k 2 = oPoint k ∧
    (PinchedNodeFibre.gScheme k) ⁻¹' {PinchedNodeFibre.pointQ k 4} = {PinchedNodeFibre.pointQ k 2} ∧
    Pcf.SchemeStalkNotFormallyEtaleAt (PinchedNodeFibre.gScheme k) (PinchedNodeFibre.pointQ k 2) ∧
    -- (6)
    oPoint k ∈ PrimeSpectrum.basicOpen (abElt k) ∧
    (∀ x : Pcf.SchemeDivisorPoint (Xs k), x.1 ∈ PrimeSpectrum.basicOpen (abElt k) →
      ((fScheme k).stalkMap x.1).hom.FormallyEtale) ∧
    ¬ ((fScheme k).stalkMap (oPoint k)).hom.Flat ∧
    -- (7)
    PinchedLift.liftMap k ≫ PinchedLift.nuB k = PinchedLift.nuB k ≫ PinchedNodeFibre.gScheme k ∧
    (∀ i : Bool, Pcf.IsSchemeUnnormalizedPCF i k (PinchedLift.structureMap k)
      (PinchedLift.liftMap k)) := by
  obtain ⟨-, -, h0, h1⟩ := postcritical_eq_and_isPCF k
  obtain ⟨-, hpre, hreg, -, -, hnot⟩ := PinchedBoundingFailure.bounding_conclusion_fails k
  exact ⟨f_isSeparableNormalizedPCF k, h0, h1,
    PinchedLine.fScheme_bPoint k, PinchedLine.bPoint_height k,
    PinchedLineScheme.bSubschemeIso_gScheme k,
    PinchedNodePCF.g_isSeparableNormalizedPCF k, PinchedNodeFibre.not_isSchemeUnnormalizedPCF k,
    PinchedSigmaExact.sigma_eq k, pointQ_not_mem_sigma k, hreg,
    PinchedSigmaExact.pointInX_two k, hpre, hnot,
    oPoint_mem_basicOpen k, f_formallyEtale_of_codimOne k,
    PinchedNotFlat.fScheme_stalkMap_not_flat k,
    PinchedLift.liftMap_comp_nuB k, PinchedLift.lift_isSchemeUnnormalizedPCF k⟩

#print axioms f_formallyEtale_of_codimOne
#print axioms pointQ_not_mem_sigma
#print axioms pinched_unnormalized_remark

end Pcf.Examples.PaperP.PinchedUnnormalizedRemark
