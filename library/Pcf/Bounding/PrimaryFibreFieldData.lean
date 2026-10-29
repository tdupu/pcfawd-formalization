/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Function-field data for the primary fibre lemma

For an extension of domains `C → B` that is generically integral, the
function-field extension `L / F` is finite. Its separable closure is generated
by a single element `θ` of `B`, whose minimal polynomial is coprime to its
derivative, and every `p^e`-th power of an element of `L` is a polynomial in
`θ` over `F`. This is the field-theoretic input of the proof of
`latex/paper-p.tex`, Lemma `lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding

open Polynomial

variable {C B F L : Type*} [CommRing C] [IsDomain C] [CommRing B] [IsDomain B]
  [Algebra C B] [FaithfulSMul C B] [Field F] [Field L]
  [Algebra C F] [IsFractionRing C F] [Algebra B L] [IsFractionRing B L]
  [Algebra F L] [Algebra C L] [IsScalarTower C F L] [IsScalarTower C B L]

/-- A generically integral finite-type extension of domains has a finite
extension of fraction fields. -/
theorem finiteDimensional_of_generic_integral [Algebra.FiniteType C B]
    (g : C) (hg : g ≠ 0)
    (hint : ∀ b : B, ∃ n : ℕ, IsIntegral C (algebraMap C B g ^ n * b)) :
    FiniteDimensional F L := by
  classical
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := C) (A := B)
  have hCB : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have halgB (b : B) : IsAlgebraic C b := by
    obtain ⟨n, hn⟩ := hint b
    have hg' : algebraMap C B g ^ n ∈ nonZeroDivisors B := by
      apply mem_nonZeroDivisors_of_ne_zero
      apply pow_ne_zero
      rw [Ne, ← map_zero (algebraMap C B)]
      exact hCB.ne hg
    exact IsAlgebraic.of_mul hg' (isAlgebraic_algebraMap _ |>.pow n) hn.isAlgebraic
  have hintL (b : B) : IsIntegral F (algebraMap B L b) := by
    have h : IsAlgebraic C (algebraMap B L b) := by
      exact (halgB b).algHom (IsScalarTower.toAlgHom C B L)
    exact ((IsFractionRing.isAlgebraic_iff C F L).mp h).isIntegral
  let S : Set L := algebraMap B L '' (T : Set B)
  have : Finite S := (T.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hintL b)
  have hmem (b : B) : algebraMap B L b ∈ IntermediateField.adjoin F S := by
    have hb : b ∈ Algebra.adjoin C (T : Set B) := by rw [hT]; trivial
    have himg := Algebra.adjoin_image C (IsScalarTower.toAlgHom C B L) (T : Set B)
    have hb' : algebraMap B L b ∈ Algebra.adjoin C S := by
      change IsScalarTower.toAlgHom C B L b ∈ _
      rw [show S = IsScalarTower.toAlgHom C B L '' (T : Set B) from rfl, himg]
      exact ⟨b, hb, rfl⟩
    have hle : Algebra.adjoin C S ≤
        ((IntermediateField.adjoin F S).toSubalgebra).restrictScalars C :=
      Algebra.adjoin_le (IntermediateField.subset_adjoin F S)
    exact hle hb'
  have htop : IntermediateField.adjoin F S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    exact div_mem (hmem b₁) (hmem b₂)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

include C in
omit [IsDomain B] [FaithfulSMul C B] in
/-- **Separable-part data.** If `B` is integrally closed and `L / F` is finite
of exponential characteristic `p`, there are `θ ∈ B`, a monic `f ∈ F[X]` with
`f(θ) = 0` and `f` coprime to `f'`, and an exponent `e` such that every
`p^e`-th power in `L` is a polynomial in `θ` over `F`. -/
theorem exists_separable_part_data [IsIntegrallyClosed B] (p : ℕ) [ExpChar F p]
    [FiniteDimensional F L] :
    ∃ (θ : B) (f a b : F[X]) (e : ℕ), f.Monic ∧ aeval (algebraMap B L θ) f = 0 ∧
      a * f + b * derivative f = 1 ∧
      ∀ y : L, ∃ P : F[X], aeval (algebraMap B L θ) P = y ^ (p ^ e) := by
  let Ls := separableClosure F L
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F Ls
  let θ₀ : L := α
  have hαint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hgen₀ (w : L) (hw : w ∈ Ls) : ∃ P : F[X], aeval θ₀ P = w := by
    have hw' : (⟨w, hw⟩ : Ls) ∈ (IntermediateField.adjoin F {α}).toSubalgebra := by
      rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hw'
    obtain ⟨P, hP⟩ := hw'
    refine ⟨P, ?_⟩
    have h : ((aeval α P : Ls) : L) = w := congrArg Subtype.val hP
    rw [← h]
    exact Polynomial.aeval_algHom_apply Ls.val α P
  have hθ₀alg : IsAlgebraic C θ₀ :=
    (IsFractionRing.isAlgebraic_iff C F L).mpr (Algebra.IsAlgebraic.isAlgebraic θ₀)
  obtain ⟨y, hy0, hyint⟩ := hθ₀alg.exists_integral_multiple
  let θL : L := y • θ₀
  have hyF : algebraMap C F y ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap C F)]
    exact (IsFractionRing.injective C F).ne hy0
  have hθL : θL = algebraMap F L (algebraMap C F y) * θ₀ := by
    rw [← IsScalarTower.algebraMap_apply]
    exact Algebra.smul_def y θ₀
  obtain ⟨θ, hθ⟩ : ∃ θ : B, algebraMap B L θ = θL :=
    IsIntegrallyClosed.isIntegral_iff.mp (hyint.tower_top (A := B))
  have hθLmem : θL ∈ Ls := by
    rw [hθL]
    exact mul_mem (Ls.algebraMap_mem _) α.2
  have hsep : IsSeparable F θL := mem_separableClosure_iff.mp hθLmem
  obtain ⟨a, b, hab⟩ := hsep
  have hθLint : IsIntegral F θL := Algebra.IsIntegral.isIntegral θL
  have : IsPurelyInseparable Ls L := separableClosure.isPurelyInseparable F L
  have : ExpChar Ls p := expChar_of_injective_algebraMap (algebraMap F Ls).injective p
  have : FiniteDimensional Ls L := FiniteDimensional.right F Ls L
  refine ⟨θ, minpoly F θL, a, b, IsPurelyInseparable.exponent Ls L, minpoly.monic hθLint,
    by rw [hθ]; exact minpoly.aeval F θL, hab, ?_⟩
  intro z
  obtain ⟨w, hw⟩ := IsPurelyInseparable.exponent_def' (K := Ls) (L := L) p z
  obtain ⟨P, hP⟩ := hgen₀ (w : L) w.2
  refine ⟨P.comp (Polynomial.C (algebraMap C F y)⁻¹ * X), ?_⟩
  rw [hθ, aeval_comp, map_mul, aeval_C, aeval_X, hθL, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hyF, map_one, one_mul, hP, ← hw]
  rfl

#print axioms finiteDimensional_of_generic_integral
#print axioms exists_separable_part_data

end Pcf.Bounding
