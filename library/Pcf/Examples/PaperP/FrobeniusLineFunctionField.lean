/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineRestriction
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The inseparable function-field restriction

The function-field map extending the actual coordinate map `u ↦ u^p` has
image `k(u^p)` in `k(u)`. The resulting extension is purely inseparable of
degree `p`, and is not separable. Scheme-stalk identifications are separate.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open Polynomial IntermediateField

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable def powerSubfield : IntermediateField k (RatFunc k) :=
  IntermediateField.adjoin k {(RatFunc.X : RatFunc k) ^ p}

omit [Fact p.Prime] [CharP k p] in
/-- The exact function-field degree in the source example. -/
theorem powerSubfield_finrank : Module.finrank (powerSubfield k p) (RatFunc k) = p := by
  unfold powerSubfield
  rw [RatFunc.finrank_eq_max_natDegree]
  have h : (RatFunc.X : RatFunc k) ^ p =
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ p) := by simp
  rw [h, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- The extension `k(u)/k(u^p)` is purely inseparable. -/
theorem powerSubfield_isPurelyInseparable :
    IsPurelyInseparable (powerSubfield k p) (RatFunc k) := by
  let F := powerSubfield k p
  haveI : IsPurelyInseparable F (IntermediateField.adjoin F {(RatFunc.X : RatFunc k)}) := by
    apply (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F (RatFunc k) p).mpr
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact ⟨⟨(RatFunc.X : RatFunc k) ^ p, IntermediateField.mem_adjoin_simple_self _ _⟩, rfl⟩
  exact (RatFunc.IntermediateField.adjoinXEquiv F).isPurelyInseparable

/-- The residue-model extension has inseparable degree exactly `p`. -/
theorem powerSubfield_finInsepDegree :
    Field.finInsepDegree (powerSubfield k p) (RatFunc k) = p := by
  letI := powerSubfield_isPurelyInseparable k p
  rw [IsPurelyInseparable.finInsepDegree_eq, powerSubfield_finrank]

/-- The Frobenius return is not separable on its explicit function-field model. -/
theorem powerSubfield_not_isSeparable : ¬ Algebra.IsSeparable (powerSubfield k p) (RatFunc k) := by
  intro hsep
  letI := hsep
  letI := powerSubfield_isPurelyInseparable k p
  have hbij := IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    (powerSubfield k p) (RatFunc k)
  have hdeg := Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hbij
  rw [powerSubfield_finrank] at hdeg
  exact (Fact.out : p.Prime).ne_one hdeg

/-- The actual coordinate map into the source rational function field. -/
noncomputable def lineCoordinateToFunctionField : Polynomial k →ₐ[k] RatFunc k :=
  (IsScalarTower.toAlgHom k (Polynomial k) (RatFunc k)).comp (lineCoordinateMap k p)

omit [CharP k p] in
theorem lineCoordinateToFunctionField_injective :
    Function.Injective (lineCoordinateToFunctionField k p) :=
  (IsFractionRing.injective (Polynomial k) (RatFunc k)).comp
    (lineCoordinateMap_injective k p (Fact.out : p.Prime).pos)

/-- The function-field extension of the actual affine-line coordinate map. -/
noncomputable def lineFunctionFieldMap : RatFunc k →ₐ[k] RatFunc k :=
  IsFractionRing.liftAlgHom (lineCoordinateToFunctionField_injective k p)

omit [CharP k p] in
@[simp] theorem lineFunctionFieldMap_on_polynomial (q : Polynomial k) :
    lineFunctionFieldMap k p (algebraMap (Polynomial k) (RatFunc k) q) =
      algebraMap (Polynomial k) (RatFunc k) (lineCoordinateMap k p q) := by
  exact IsFractionRing.lift_algebraMap (lineCoordinateToFunctionField_injective k p) q

omit [CharP k p] in
@[simp] theorem lineFunctionFieldMap_X :
    lineFunctionFieldMap k p (RatFunc.X : RatFunc k) = (RatFunc.X : RatFunc k) ^ p := by
  rw [← RatFunc.algebraMap_X, lineFunctionFieldMap_on_polynomial, lineCoordinateMap_X, map_pow]

omit [CharP k p] in
/-- The image of the actual function-field map is exactly `k(u^p)`.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineFunctionFieldMap_fieldRange :
    (lineFunctionFieldMap k p).fieldRange = powerSubfield k p := by
  rw [AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X, IntermediateField.adjoin_map]
  simp [powerSubfield]

/-- Pure inseparability for the actual fraction-field extension of the
coordinate map, with its induced scalar structure. -/
theorem lineFunctionFieldMap_isPurelyInseparable :
    letI := (lineFunctionFieldMap k p).toRingHom.toAlgebra
    IsPurelyInseparable (RatFunc k) (RatFunc k) := by
  have hpow (x : RatFunc k) : ∃ n : ℕ, x ^ p ^ n ∈ powerSubfield k p := by
    obtain ⟨n, y, hy⟩ := (isPurelyInseparable_iff_pow_mem (powerSubfield k p) p).mp
      (powerSubfield_isPurelyInseparable k p) x
    refine ⟨n, ?_⟩
    rw [← hy]
    exact y.2
  letI := (lineFunctionFieldMap k p).toRingHom.toAlgebra
  apply (isPurelyInseparable_iff_pow_mem (RatFunc k) p).mpr
  intro x
  obtain ⟨n, hn⟩ := hpow x
  refine ⟨n, ?_⟩
  change x ^ p ^ n ∈ (lineFunctionFieldMap k p).fieldRange
  rwa [lineFunctionFieldMap_fieldRange]

private theorem fieldRange_isSeparable_of_hom {k K E : Type*} [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] (f : K →ₐ[k] E)
    (h : letI := f.toRingHom.toAlgebra; Algebra.IsSeparable K E) :
    Algebra.IsSeparable f.fieldRange E := by
  letI := f.toRingHom.toAlgebra
  letI := h
  letI : Algebra K f.fieldRange := f.rangeRestrict.toRingHom.toAlgebra
  haveI : IsScalarTower K f.fieldRange E := IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.isSeparable_tower_top_of_isSeparable K f.fieldRange E

/-- The actual fraction-field extension of the affine Frobenius restriction
is not separable; its image is identified above with `k(u^p)`.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineFunctionFieldMap_not_isSeparable :
    letI := (lineFunctionFieldMap k p).toRingHom.toAlgebra
    ¬ Algebra.IsSeparable (RatFunc k) (RatFunc k) := by
  intro hsep
  have hs := fieldRange_isSeparable_of_hom (lineFunctionFieldMap k p) hsep
  rw [lineFunctionFieldMap_fieldRange] at hs
  exact powerSubfield_not_isSeparable k p hs

#print axioms powerSubfield_finrank
#print axioms powerSubfield_isPurelyInseparable
#print axioms powerSubfield_finInsepDegree
#print axioms powerSubfield_not_isSeparable
#print axioms lineFunctionFieldMap_on_polynomial
#print axioms lineFunctionFieldMap_fieldRange
#print axioms lineFunctionFieldMap_not_isSeparable
#print axioms lineFunctionFieldMap_isPurelyInseparable

end Pcf.Examples.PaperP.FrobeniusLine
