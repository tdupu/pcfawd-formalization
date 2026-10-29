/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPProjectiveFinite
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Dominance of the projective morphism defined by homogeneous forms
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
attribute [local instance] specializationOrder

/-- Stacks Lemma 29.21.8, implication `(1) ⇒ (2)`: the scheme fibers of
a locally quasi-finite morphism are discrete.

Divergence from Stacks: this declaration is only the indicated forward
implication of the three-way equivalence. -/
@[stacks 06RT "(1) ⇒ (2)"]
theorem schemeHom_discreteFibers_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : LocallyQuasiFinite f) : ∀ y : Y, DiscreteTopology (f.fiber y) := by
  let := hf
  intro y
  infer_instance

/-- Discrete fibers prevent a locally quasi-finite map from collapsing a
strict specialization. -/
theorem schemeHom_strictMono_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    StrictMono f := by
  intro x y hxy
  have hmono := f.continuous.specialization_monotone
  refine lt_of_le_not_ge (hmono hxy.le) ?_
  intro hyx
  have heq : f x = f y := le_antisymm (hmono hxy.le) hyx
  let := schemeHom_discreteFibers_of_locallyQuasiFinite f inferInstance (f x)
  have hdisc : _root_.IsDiscrete (f ⁻¹' {f x}) := by
    simpa [Scheme.Hom.range_fiberι] using
      (isDiscrete_univ_iff.mpr inferInstance).image (f.fiberι (f x)).isEmbedding.toIsInducing
  have hpoints : y = x := hdisc.eq_of_specializes
    hxy.le (by simpa using heq.symm) rfl
  exact hxy.ne hpoints.symm

/-- A locally quasi-finite endomorphism of an irreducible scheme of finite
specialization dimension fixes its generic point. -/
theorem genericPoint_map_eq_of_locallyQuasiFinite
    {X : Scheme.{u}} [IrreducibleSpace X] [FiniteDimensionalOrder X]
    (f : X ⟶ X) [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    f (genericPoint X) = genericPoint X := by
  have hmono := schemeHom_strictMono_of_locallyQuasiFinite f
  have hheight := Order.height_le_height_apply_of_strictMono f hmono (genericPoint X)
  have hle : f (genericPoint X) ≤ genericPoint X := genericPoint_specializes _
  by_contra hne
  have hlt : f (genericPoint X) < genericPoint X := lt_of_le_of_ne hle hne
  have hfin : Order.height (f (genericPoint X)) < ⊤ := by
    rw [← WithBot.coe_lt_coe]
    exact (Order.height_le_krullDim _).trans_lt
      Order.krullDim_ne_top_of_finiteDimensionalOrder.lt_top
  exact (not_lt_of_ge hheight) (Order.height_strictMono hlt hfin)

/-- A locally quasi-finite endomorphism of an irreducible scheme of finite
specialization dimension is dominant. -/
theorem schemeHom_isDominant_of_locallyQuasiFinite
    {X : Scheme.{u}} [IrreducibleSpace X] [FiniteDimensionalOrder X]
    (f : X ⟶ X) [LocallyQuasiFinite f] [LocallyOfFiniteType f] : IsDominant f := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← genericPoint_closure X]
  apply closure_mono
  intro x hx
  have heq : x = genericPoint X := Set.mem_singleton_iff.mp hx
  exact ⟨genericPoint X, (genericPoint_map_eq_of_locallyQuasiFinite f).trans heq.symm⟩

variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- Forgetting homogeneity embeds the specialization order of projective
points into the dual inclusion order of polynomial prime ideals. -/
noncomputable def paperPProjectivePrimeOrderEmbedding :
    (AlgebraicGeometry.Proj polyGrade) ↪o (PrimeSpectrum (MvPolynomial (Fin n ⊕ Unit) K))ᵒᵈ where
  toFun x := ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩
  inj' := by
    intro x y h
    apply ProjectiveSpectrum.ext
    exact HomogeneousIdeal.toIdeal_injective (PrimeSpectrum.ext_iff.mp h)
  map_rel_iff' := by
    intro x y
    change y.asHomogeneousIdeal ≤ x.asHomogeneousIdeal ↔ y ⤳ x
    rw [specializes_iff_mem_closure]
    exact ProjectiveSpectrum.le_iff_mem_closure polyGrade y x

/-- The actual projective scheme has finite specialization dimension. -/
instance paperPProjective_finiteDimensionalOrder :
    FiniteDimensionalOrder (AlgebraicGeometry.Proj polyGrade) := by
  apply Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
  constructor
  · exact Order.krullDim_ne_bot_iff.mpr inferInstance
  · have hbound := Order.krullDim_le_of_strictMono _
      (paperPProjectivePrimeOrderEmbedding (K := K) (n := n)).strictMono
    have hpoly : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n ⊕ Unit) K))ᵒᵈ < ⊤ := by
      rw [Order.krullDim_orderDual]
      change ringKrullDim (MvPolynomial (Fin n ⊕ Unit) K) < ⊤
      simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_unit, zero_add]
      rw [Nat.cast_add, Nat.cast_one]
      change ((n : ℕ∞) + 1 : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞)
      exact WithBot.coe_lt_coe.mpr (by simp)
    exact ne_top_of_lt (hbound.trans_lt hpoly)

/-- Every basepoint-free positive-degree family of homogeneous forms
defines a dominant global projective scheme morphism.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
instance paperPFormsProjective_isDominant
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) :
    IsDominant (paperPFormsProjectiveSchemeMap F d hd hF hcover) :=
  schemeHom_isDominant_of_locallyQuasiFinite _

#print axioms schemeHom_strictMono_of_locallyQuasiFinite
#print axioms schemeHom_discreteFibers_of_locallyQuasiFinite
#print axioms genericPoint_map_eq_of_locallyQuasiFinite
#print axioms schemeHom_isDominant_of_locallyQuasiFinite
#print axioms paperPProjectivePrimeOrderEmbedding
#print axioms paperPProjective_finiteDimensionalOrder
#print axioms paperPFormsProjective_isDominant
end Pcf
