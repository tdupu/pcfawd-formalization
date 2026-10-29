/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FerrandPushoutAffine
public import Pcf.Examples.PaperP.MonodromyLossCurveScheme
public import Mathlib.Tactic.ComputeDegree

/-!
# The affine pinching charts of `E × {0}` along `y` (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss`: "Pinch `E × {0}` along `y : E → ℙ¹` ... using the
finite pushout construction of [Fer03, §5.4]."

On the chart `E_A × 𝔸¹_z = Spec A[z]` (finite chart `A = k[x,y]/(y² - x³ + x)`), the divisor
`E × {0}` is `Spec A` (`z = 0`), and `y` restricts to `Spec A → 𝔸¹_y = Spec k[y]`. On the chart at
infinity `E_B × 𝔸¹_z = Spec B[z]` (`B = k[w,s]/(s³ - w²s - w)`, `w = 1/y`), `y` restricts to
`Spec B → Spec k[w]`, the other chart of `ℙ¹`. Both restrictions are finite:

* `betaA_isIntegral`: `A` is integral over `k[y]` (`x³ - x - y² = 0` is monic in `x`);
* `betaB_isIntegral`: `B` is integral over `k[w]` (`s³ - w²s - w` is monic in `s`).

`FerrandPushout.isPushout` then shows that the pinched charts `Spec(k[y] ×_A A[z])` and
`Spec(k[w] ×_B B[z])` are pushouts in the category of all schemes (`isPushout_A`,
`isPushout_B`). These are the two affine pieces of the pinching of `E × 𝔸¹_z` along `E × {0}`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.MonodromyLossPinch

open Polynomial AlgebraicGeometry CategoryTheory Limits
open Pcf.Examples.PaperP.MonodromyLossCurve

universe u

variable (k : Type u) [Field k]

/-- `z ↦ 0`: `A[z] → A`, the divisor `E_A × {0}`. -/
noncomputable def piA : Polynomial (A k) →+* A k := Polynomial.evalRingHom 0

theorem piA_surjective : Function.Surjective (piA k) := fun a => ⟨C a, by simp [piA]⟩

/-- `y : Spec A → Spec k[y]`, i.e. `k[y] → A`, `y ↦ y`. -/
noncomputable def betaA : Polynomial k →+* A k := eval₂RingHom (algebraMap k (A k)) (yA k)

theorem betaA_C (c : k) : betaA k (C c) = algebraMap k (A k) c := by simp [betaA]

theorem betaA_X : betaA k X = yA k := by simp [betaA]

/-- `x` is integral over `k[y]`: it is a root of `T³ - T - y²`. -/
theorem xA_isIntegralElem : (betaA k).IsIntegralElem (xA k) := by
  refine ⟨X ^ 3 - X - C (X ^ 2), by monicity!, ?_⟩
  simp only [eval₂_sub, eval₂_X, eval₂_pow, eval₂_C, map_pow, betaA_X]
  linear_combination -(A_rel k)

/-- **`A` is integral over `k[y]`**, so `y : E_A → 𝔸¹` is finite. -/
theorem betaA_isIntegral : (betaA k).IsIntegral := by
  have hconst : ∀ c : k, (betaA k).IsIntegralElem (algebraMap k (A k) c) := fun c => by
    rw [← betaA_C]; exact (betaA k).isIntegralElem_map
  have hy : (betaA k).IsIntegralElem (yA k) := by
    rw [← betaA_X]; exact (betaA k).isIntegralElem_map
  have hof : ∀ q : Polynomial k,
      (betaA k).IsIntegralElem (AdjoinRoot.of (W k).polynomial q) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => exact (by simpa [AdjoinRoot.algebraMap_eq'] using hconst c)
    | add p q hp hq => rw [map_add]; exact RingHom.IsIntegralElem.add _ hp hq
    | monomial n c hn =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact RingHom.IsIntegralElem.mul _ hn (by simpa [xA] using xA_isIntegralElem k)
  intro a
  induction a using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C q => rw [AdjoinRoot.mk_C]; exact hof q
    | add p q hp hq => rw [map_add]; exact RingHom.IsIntegralElem.add _ hp hq
    | monomial n q hn =>
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      exact RingHom.IsIntegralElem.mul _ hn (by simpa [yA] using hy)

/-- `z ↦ 0`: `B[z] → B`. -/
noncomputable def piB : Polynomial (B k) →+* B k := Polynomial.evalRingHom 0

theorem piB_surjective : Function.Surjective (piB k) := fun a => ⟨C a, by simp [piB]⟩

/-- `w = 1/y : Spec B → Spec k[w]`, i.e. `k[w] → B`. -/
noncomputable def betaB : Polynomial k →+* B k := AdjoinRoot.of (fB k)

theorem betaB_X : betaB k X = wB k := rfl

/-- **`B` is integral over `k[w]`**, so `y : E_B → ℙ¹ ∖ {0}` is finite. -/
theorem betaB_isIntegral : (betaB k).IsIntegral := by
  have : Module.Finite (Polynomial k) (B k) :=
    (AdjoinRoot.powerBasis' (fB_monic k)).finite
  have : Algebra.IsIntegral (Polynomial k) (B k) := inferInstance
  exact fun b => Algebra.IsIntegral.isIntegral (R := Polynomial k) b

/-- The pinched chart ring `k[y] ×_A A[z] = k[y] + z A[z]`. -/
abbrev RA := FerrandPushout.Fib (piA k) (betaA k)

/-- The pinched chart ring `k[w] ×_B B[z] = k[w] + z B[z]`. -/
abbrev RB := FerrandPushout.Fib (piB k) (betaB k)

/-- **The pinched chart `Spec(k[y] ×_A A[z])` is the pushout of
`Spec k[y] ← Spec A → Spec A[z]` in `Scheme`.** -/
theorem isPushout_A :
    IsPushout (Spec.map (CommRingCat.ofHom (piA k))) (Spec.map (CommRingCat.ofHom (betaA k)))
      (Spec.map (CommRingCat.ofHom (FerrandPushout.pr₂ (piA k) (betaA k))))
      (Spec.map (CommRingCat.ofHom (FerrandPushout.pr₁ (piA k) (betaA k)))) :=
  FerrandPushout.isPushout (piA_surjective k) (betaA_isIntegral k)

/-- **The pinched chart `Spec(k[w] ×_B B[z])` is the pushout of
`Spec k[w] ← Spec B → Spec B[z]` in `Scheme`.** -/
theorem isPushout_B :
    IsPushout (Spec.map (CommRingCat.ofHom (piB k))) (Spec.map (CommRingCat.ofHom (betaB k)))
      (Spec.map (CommRingCat.ofHom (FerrandPushout.pr₂ (piB k) (betaB k))))
      (Spec.map (CommRingCat.ofHom (FerrandPushout.pr₁ (piB k) (betaB k)))) :=
  FerrandPushout.isPushout (piB_surjective k) (betaB_isIntegral k)

#print axioms betaA_isIntegral
#print axioms betaB_isIntegral
#print axioms isPushout_A
#print axioms isPushout_B

end Pcf.Examples.PaperP.MonodromyLossPinch
