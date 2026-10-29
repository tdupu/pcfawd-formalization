/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryPolynomialCoefficientStage
public import Mathlib.Algebra.Polynomial.Expand

/-!
# The inseparable-degree reduction step

This module isolates the field-theoretic mechanism in Stacks Project,
Tag 04KM. When the coefficients of the minimal polynomial of a separable
element acquire `p`th roots, its prescribed `p`th root becomes separable.
This places one previously inseparable generator into the new separable
subfield, the key step before the strict degree inequality.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open scoped IntermediateField

/-- Stacks Project, Tag 04KM, uses this instance of the `p`th-root
criterion (Fields, Lemma 9.28.2): if the minimal polynomial of `α`
has coefficientwise `p`th roots over the base and `β^p = α`, then
`β` is separable over that base. -/
theorem isSeparable_pth_root_of_minpoly_coeff_roots
    (F M : Type*) [Field F] [Field M] [Algebra F M]
    (p : ℕ) [Fact p.Prime] [CharP F p] [CharP M p]
    (α β : M) (hβ : β ^ p = α) (hα : IsSeparable F α)
    (Q : Polynomial F)
    (hQ : Q.map (frobenius F p) = minpoly F α) :
    IsSeparable F β := by
  have hsepQ : Q.Separable :=
    (Polynomial.separable_map (frobenius F p)).mp (hQ ▸ hα)
  have hpoly : Polynomial.expand F p (minpoly F α) = Q ^ p := by
    rw [← hQ, ← Polynomial.map_expand, Polynomial.map_frobenius_expand]
  have hroot : Polynomial.aeval β Q = 0 := by
    have hpow : (Polynomial.aeval β Q) ^ p = 0 := by
      calc
        (Polynomial.aeval β Q) ^ p = Polynomial.aeval β (Q ^ p) := by
          rw [map_pow]
        _ = Polynomial.aeval β (Polynomial.expand F p (minpoly F α)) := by
          rw [hpoly]
        _ = Polynomial.aeval (β ^ p) (minpoly F α) :=
          Polynomial.expand_aeval p (minpoly F α) β
        _ = 0 := by rw [hβ]; exact minpoly.aeval F α
    exact eq_zero_of_pow_eq_zero hpow
  exact hsepQ.of_dvd (minpoly.dvd F β hroot)

/-- Adjoining a genuinely new element to the intermediate base strictly
decreases the remaining finite extension degree. In Tag 04KM the new
element is the `p`th root that becomes separable after coefficient-root
alteration. -/
theorem finrank_strict_drop_of_adjoin_new_element
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (β : K)
    (hβ : β ∉ (⊥ : IntermediateField F K)) :
    Module.finrank (F⟮β⟯) K < Module.finrank F K := by
  have hdegree : 1 < Module.finrank F F⟮β⟯ := by
    have hne : Module.finrank F F⟮β⟯ ≠ 1 :=
      mt (IntermediateField.finrank_adjoin_simple_eq_one_iff (F := F) (α := β)).mp hβ
    have hpos : 0 < Module.finrank F F⟮β⟯ := Module.finrank_pos
    omega
  have hremain : 0 < Module.finrank (F⟮β⟯) K := Module.finrank_pos
  calc
    Module.finrank (F⟮β⟯) K =
        1 * Module.finrank (F⟮β⟯) K := (one_mul _).symm
    _ < Module.finrank F (F⟮β⟯) * Module.finrank (F⟮β⟯) K :=
      Nat.mul_lt_mul_of_pos_right hdegree hremain
    _ = Module.finrank F K := Module.finrank_mul_finrank F (F⟮β⟯) K

/-- If a finite extension contains an element outside its maximal separable
subextension, adjoining that element to the separable subfield strictly
reduces the remaining inseparable degree. -/
theorem finInsepDegree_strict_bound_after_adjoining_nonseparable_element
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (β : K)
    (hβ : β ∉ separableClosure F K) :
    Module.finrank ((separableClosure F K)⟮β⟯) K <
      Field.finInsepDegree F K := by
  have hnotbot : β ∉ (⊥ : IntermediateField (separableClosure F K) K) := by
    intro h
    obtain ⟨s, hs⟩ := IntermediateField.mem_bot.mp h
    exact hβ (hs ▸ s.property)
  exact finrank_strict_drop_of_adjoin_new_element
    (separableClosure F K) K β hnotbot

#print axioms isSeparable_pth_root_of_minpoly_coeff_roots
#print axioms finrank_strict_drop_of_adjoin_new_element
#print axioms finInsepDegree_strict_bound_after_adjoining_nonseparable_element

end Pcf.Bounding.PrimaryFibres
