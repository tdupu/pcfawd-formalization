/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingDimensionZero
public import Pcf.Palomar.Bridge

/-!
# Dimension-one PCF all the way down

The dimension-one paragraph after `def:pcfawd` in `paper.tex`.
The proof uses strict specialization chains and the dimension-zero base case,
not the global PCFAWD or all-subvarieties theorem.
-/

@[expose] public section

universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace Pcf.PaperCharZero

attribute [local instance] specializationOrder

/-- An integral effective divisor lowers any finite dimension bound by at
least one. This general inequality needs no finite-type or catenarity premise. -/
theorem divisorClosure_dimension_le
    {X : Scheme.{u}} [IsIntegral X] (A : SchemeDivisorPoint X) (n : ℕ)
    (hX : topologicalKrullDim X ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (pointClosureIdealSheaf A.1).subscheme ≤ (n : WithBot ℕ∞) := by
  rw [← scheme_orderKrullDim_eq_topologicalKrullDim, Order.krullDim]
  apply iSup_le
  intro p
  let ι := (pointClosureIdealSheaf A.1).subschemeι
  have hstrict : StrictMono ι :=
    ι.continuous.specialization_monotone.strictMono_of_injective
      ι.isClosedEmbedding.injective
  let q := p.map ι hstrict
  have hlast : q.last ≤ A.1 := by
    have h := ι.continuous.specialization_monotone (genericPoint_specializes p.last)
    rwa [pointClosureSubscheme_genericPoint] at h
  let t := q.snoc (genericPoint X) (lt_of_le_of_lt hlast A.lt_genericPoint)
  have hdim := (Order.LTSeries.length_le_krullDim t).trans
    ((scheme_orderKrullDim_eq_topologicalKrullDim (X := X)).le.trans hX)
  have hlen : p.length + 1 ≤ n + 1 := by
    apply ENat.natCast_le_natCast.mp
    apply WithBot.coe_le_coe.mp
    simpa [t, q] using hdim
  exact_mod_cast Nat.le_of_add_le_add_right hlen

/-- On an integral scheme of dimension at most one, the reduced closure of
every integral effective divisor has dimension exactly zero. -/
theorem divisorClosure_dimension_zero_of_le_one
    {X : Scheme.{u}} [IsIntegral X] (A : SchemeDivisorPoint X)
    (hX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    topologicalKrullDim (pointClosureIdealSheaf A.1).subscheme = 0 := by
  apply le_antisymm (divisorClosure_dimension_le A 0 hX)
  rw [← scheme_orderKrullDim_eq_topologicalKrullDim]
  exact Order.krullDim_nonneg

/-- Exact one-step dimension drop in the dimension-one case. -/
theorem divisorClosure_dimension_add_one_eq_of_dimension_one
    {X : Scheme.{u}} [IsIntegral X] (A : SchemeDivisorPoint X)
    (hX : topologicalKrullDim X = (1 : WithBot ℕ∞)) :
    topologicalKrullDim (pointClosureIdealSheaf A.1).subscheme + 1 = topologicalKrullDim X := by
  rw [divisorClosure_dimension_zero_of_le_one A hX.le, zero_add, hX]

/-- The depth-one recursion on a curve is exactly ambient PCF: each child is
zero-dimensional, hence automatically PCF. No restriction-PCF theorem is used. -/
theorem dimension_one_depth_one_iff_pcf
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    SchemePCFAllTheWayDownAtDepth k 1 s f ↔ IsNormalizedPCFOfFiniteType k s f := by
  constructor
  · exact fun h ↦ h.1
  · intro hpcf
    refine ⟨hpcf, ?_⟩
    intro A r p hp hA
    let B := schemeDivisorIterateOfFiniteType k s f r A
    apply dimension_zero_isNormalizedPCFOfFiniteType
    exact (divisorClosure_dimension_zero_of_le_one B hX).le

/-- `u:dimension-one`: PCF all the way down is equivalent to PCF in dimension
at most one, directly from the base case and finite-dimensional termination. -/
theorem dimension_one_pcfAllTheWayDown_iff_pcf
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    SchemePCFAllTheWayDown k s f ↔ IsNormalizedPCFOfFiniteType k s f :=
  (pcfAllTheWayDown_iff_at_dimension_bound k 1 s f hX).trans
    (dimension_one_depth_one_iff_pcf k s f hX)

/-- The same equivalence for the manuscript-facing Palomar predicates, without
using the global headline theorem. -/
theorem dimension_one_palomar_pcfAllTheWayDown_iff_pcf
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    Palomar.PCFAllTheWayDown f ↔ Palomar.IsNormalizedPCF f :=
  (Palomar.pcfAllTheWayDown_iff_scheme k s f).trans
    ((dimension_one_pcfAllTheWayDown_iff_pcf k s f hX).trans
      (Palomar.isNormalizedPCF_iff_scheme k s f).symm)

/-- Source-facing dimension-one assertion for an integral finite-type variety
and an actual finite-surjective endomorphism. Noetherian hypotheses are derived,
and the equivalence is independent of the global headline theorem. -/
theorem curve_pcfAllTheWayDown_iff_pcf
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    (f : X ⟶ X) [IsFinite f] [Surjective f]
    (hX : topologicalKrullDim X = (1 : WithBot ℕ∞)) :
    Palomar.PCFAllTheWayDown f ↔ Palomar.IsNormalizedPCF f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let : IsNoetherian X := {}
  exact dimension_one_palomar_pcfAllTheWayDown_iff_pcf k s f hX.le

end Pcf.PaperCharZero
