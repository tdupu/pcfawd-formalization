/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Defs
public import Pcf.Stacks.Abhyankar.StandardCoverNormalization
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The rings of Stacks Example 58.31.4 (Tag `0EYF`)

API for `standardRing A f e = A[x]/(x^e - f)` and `standardTameRing A f e = C_f`:

* `standardTameRingEquiv`: for `f = u a` with `u` a unit, `C_f ≅ A_a[x]/(x^e - u a)`, the form
  in which phase 1 (`localizedStandardPoly`) writes the pieces;
* `standardRingOneOneEquiv`, `standardTameRingOneOneEquiv`: for `f = 1`, `e = 1` both rings are
  `A` (the pieces of a split finite étale cover, the case `x ∉ D` of the proof of `0EYG`);
* `isStandardTameData_unit_mul`, `isStandardTameData_one_one`: the hypotheses of Example
  58.31.4 for these data.
-/

@[expose] public section

universe u

open Polynomial

namespace Pcf.Stacks.SchemeLevel

variable {A : Type u} [CommRing A]

/-- For `f = u a` with `u` a unit, `C_f = (A[x]/(x^e - u a))_{ua}` is `A_a[x]/(x^e - u a)`. -/
noncomputable def standardTameRingEquiv (u : Aˣ) (a : A) (e : ℕ) :
    standardTameRing A ((u : A) * a) e ≃ₐ[A] AdjoinRoot (localizedStandardPoly u a e) := by
  have : IsLocalization.Away (algebraMap A (standardRing A ((u : A) * a) e) a)
      (standardTameRing A ((u : A) * a) e) := by
    have hassoc : Associated (algebraMap A (standardRing A ((u : A) * a) e) ((u : A) * a))
        (algebraMap A (standardRing A ((u : A) * a) e) a) :=
      Associated.symm ⟨Units.map (algebraMap A (standardRing A ((u : A) * a) e)).toMonoidHom u,
        (mul_comm _ _).trans (map_mul _ _ _).symm⟩
    exact IsLocalization.Away.of_associated hassoc
  exact ((IsLocalization.algEquiv
    (Submonoid.powers (algebraMap A (standardRing A ((u : A) * a) e) a))
    (standardTameRing A ((u : A) * a) e)
    (Localization.Away (algebraMap A (standardRing A ((u : A) * a) e) a))).restrictScalars
      A).trans (standardCoverLocalizationEquiv u a e)

/-- `A[x]/(x - 1) ≅ A`. -/
noncomputable def standardRingOneOneEquiv : standardRing A 1 1 ≃ₐ[A] A :=
  (Ideal.quotientEquivAlgOfEq A (by rw [pow_one])).trans (quotientSpanXSubCAlgEquiv (1 : A))

/-- `(A[x]/(x - 1))_1 ≅ A`. -/
noncomputable def standardTameRingOneOneEquiv : standardTameRing A 1 1 ≃ₐ[A] A := by
  have : IsLocalization.Away (1 : standardRing A 1 1) (standardTameRing A 1 1) := by
    simpa using (inferInstance : IsLocalization.Away
      (algebraMap A (standardRing A 1 1) 1) (standardTameRing A 1 1))
  exact ((IsLocalization.atOne (standardRing A 1 1)
    (standardTameRing A 1 1)).symm.restrictScalars A).trans standardRingOneOneEquiv

/-- The data `(A, u a, e)` satisfy the hypotheses of Example 58.31.4 when `A` is Noetherian,
`a` a nonzerodivisor with `A/(a)` reduced, `u` a unit and `e ≥ 1` invertible. -/
theorem isStandardTameData_unit_mul [IsNoetherianRing A] (u : Aˣ) {a : A}
    (ha : a ∈ nonZeroDivisors A) (hred : IsReduced (A ⧸ Ideal.span {a})) {e : ℕ} (he : 1 ≤ e)
    (heu : IsUnit (e : A)) : IsStandardTameData A ((u : A) * a) e := by
  refine ⟨inferInstance, ?_, ?_, he, heu⟩
  · exact mul_mem (Units.isUnit u).mem_nonZeroDivisors ha
  · rwa [Ideal.span_singleton_mul_left_unit (Units.isUnit u)]

/-- `(A, 1, 1)` satisfies the hypotheses of Example 58.31.4 for Noetherian `A`. -/
theorem isStandardTameData_one_one [IsNoetherianRing A] : IsStandardTameData A 1 1 := by
  refine ⟨inferInstance, one_mem _, ?_, le_rfl, by simp⟩
  have : Subsingleton (A ⧸ Ideal.span {(1 : A)}) := by
    rw [Ideal.span_singleton_one]; infer_instance
  infer_instance

#print axioms standardTameRingEquiv
#print axioms standardRingOneOneEquiv
#print axioms standardTameRingOneOneEquiv
#print axioms isStandardTameData_unit_mul
#print axioms isStandardTameData_one_one

end Pcf.Stacks.SchemeLevel
