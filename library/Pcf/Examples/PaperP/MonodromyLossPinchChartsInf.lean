/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPinchCharts
public import Pcf.Examples.PaperP.MonodromyLossPhi

/-!
# The finite-part pinching chart of `E × {∞}` along `y ∘ φ` (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss`: "Pinch ... `E × {∞}` along `y ∘ φ : E → ℙ¹`".

`φ = 1 + ι` sends `O` and `T = (0, 0)` to `O`, so `(y ∘ φ)⁻¹(𝔸¹_y) = E ∖ {O, T} = D(x) ⊂ Spec A`,
and on it `φ` is the chart piece `phi1 : A → A[1/x]` (`x ↦ i(x² - 1)/x`). This file shows:

* `phi1_isIntegral`: `A[1/x]` is integral over `A` through `phi1` (`φ` is finite over `U_A`):
  `x` is a root of `T² + i x₃ T - 1` with `x₃ = phi1 x`, `1/x = x + i x₃`, and `y² = x³ - x`;
* `betaInf_isIntegral`: `y ∘ φ : k[y] → A[1/x]` is integral;
* `isPushout_inf`: the pinched chart `Spec(k[y] ×_{A[1/x]} A[1/x][t])` (`t = 1/z`) is the pushout
  of `Spec k[y] ← Spec A[1/x] → Spec A[1/x][t]` in `Scheme`.

The other chart of this pinching must contain both `O` and `T` (both map to `∞` under `y ∘ φ`),
so it is not a subset of either chart `U_A`, `U_B` of `E`; it is not constructed here.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.MonodromyLossPinch

open Polynomial AlgebraicGeometry CategoryTheory Limits
open Pcf.Examples.PaperP.MonodromyLossCurve

universe u

section Helpers

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem isIntegralElem_pow {x : S} (h : f.IsIntegralElem x) (n : ℕ) : f.IsIntegralElem (x ^ n) := by
  let := f.toAlgebra
  exact IsIntegral.pow h n

theorem isIntegralElem_sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x - y) := by
  let := f.toAlgebra
  exact IsIntegral.sub hx hy

theorem isIntegralElem_of_sq {x : S} (h : f.IsIntegralElem (x ^ 2)) : f.IsIntegralElem x := by
  let := f.toAlgebra
  exact IsIntegral.of_pow two_pos h

end Helpers

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

local notation "X₀" => algebraMap (A k) (Ax k) (xA k)
local notation "Y₀" => algebraMap (A k) (Ax k) (yA k)

omit [CharP k 3] in
theorem x_mul_invX : X₀ * invX k = 1 := IsLocalization.Away.mul_invSelf (xA k)

include hi

theorem phi1_xA : phi1 k i hi (xA k) = algebraMap k (Ax k) i * (X₀ ^ 2 - 1) * invX k := by
  simp [phi1, liftA_x]

theorem phi1_const (c : k) : phi1 k i hi (algebraMap k (A k) c) = algebraMap k (Ax k) c :=
  liftA_algebraMap k _ _ _ c

omit [CharP k 3] in
theorem i_sq : algebraMap k (Ax k) i ^ 2 = -1 := by rw [← map_pow, hi]; simp

/-- `x` is integral over `A` through `phi1`: a root of `T² + i x₃ T - 1`. -/
theorem x_isIntegralElem : (phi1 k i hi).IsIntegralElem X₀ := by
  refine ⟨X ^ 2 + C (algebraMap k (A k) i * xA k) * X - 1, by monicity!, ?_⟩
  have hu := x_mul_invX k
  have h2 := i_sq k i hi
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C, eval₂_one, map_mul,
    phi1_const, phi1_xA]
  linear_combination (algebraMap k (Ax k) i ^ 2 * (X₀ ^ 2 - 1)) * hu + (X₀ ^ 2 - 1) * h2

/-- `1/x = x + i x₃`. -/
theorem invX_eq : invX k = X₀ + algebraMap k (Ax k) i * phi1 k i hi (xA k) := by
  have hu := x_mul_invX k
  have h2 := i_sq k i hi
  rw [phi1_xA]
  linear_combination X₀ * hu - (X₀ ^ 2 - 1) * invX k * h2

theorem invX_isIntegralElem : (phi1 k i hi).IsIntegralElem (invX k) := by
  rw [invX_eq k i hi]
  refine RingHom.IsIntegralElem.add _ (x_isIntegralElem k i hi) ?_
  rw [← phi1_const k i hi, ← map_mul]
  exact (phi1 k i hi).isIntegralElem_map

theorem y_isIntegralElem : (phi1 k i hi).IsIntegralElem Y₀ := by
  have hx := x_isIntegralElem k i hi
  have h : Y₀ ^ 2 = X₀ ^ 3 - X₀ := by rw [← map_pow, A_rel, map_sub, map_pow]
  refine isIntegralElem_of_sq _ ?_
  rw [h]
  exact isIntegralElem_sub _ (isIntegralElem_pow _ hx 3) hx

theorem algebraMap_isIntegralElem (a : A k) :
    (phi1 k i hi).IsIntegralElem (algebraMap (A k) (Ax k) a) := by
  have hconst : ∀ c : k, (phi1 k i hi).IsIntegralElem (algebraMap (A k) (Ax k)
      (algebraMap k (A k) c)) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← phi1_const k i hi]
    exact (phi1 k i hi).isIntegralElem_map
  have hof : ∀ q : Polynomial k, (phi1 k i hi).IsIntegralElem
      (algebraMap (A k) (Ax k) (AdjoinRoot.of (W k).polynomial q)) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => exact (by simpa [AdjoinRoot.algebraMap_eq'] using hconst c)
    | add p q hp hq => rw [map_add, map_add]; exact RingHom.IsIntegralElem.add _ hp hq
    | monomial n c hn =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul]
      exact RingHom.IsIntegralElem.mul _ hn (by simpa [xA] using x_isIntegralElem k i hi)
  induction a using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C q => rw [AdjoinRoot.mk_C]; exact hof q
    | add p q hp hq => rw [map_add, map_add]; exact RingHom.IsIntegralElem.add _ hp hq
    | monomial n q hn =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, AdjoinRoot.mk_X]
      exact RingHom.IsIntegralElem.mul _ hn (by simpa [yA] using y_isIntegralElem k i hi)

/-- **`φ` is finite over `U_A`**: `A[1/x]` is integral over `A` through `phi1`. -/
theorem phi1_isIntegral : (phi1 k i hi).IsIntegral := by
  intro z
  obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (xA k)) z
  have spec := IsLocalization.mk'_spec (Ax k) a
    (⟨xA k ^ n, n, rfl⟩ : Submonoid.powers (xA k))
  have hu := x_mul_invX k
  have hz : IsLocalization.mk' (Ax k) a (⟨xA k ^ n, n, rfl⟩ : Submonoid.powers (xA k)) =
      algebraMap (A k) (Ax k) a * invX k ^ n := by
    rw [← spec]
    simp only [map_pow]
    calc _ = IsLocalization.mk' (Ax k) a (⟨xA k ^ n, n, rfl⟩ : Submonoid.powers (xA k)) *
          (X₀ * invX k) ^ n := by rw [hu, one_pow, mul_one]
      _ = _ := by ring
  rw [hz]
  exact RingHom.IsIntegralElem.mul _ (algebraMap_isIntegralElem k i hi a)
    (isIntegralElem_pow _ (invX_isIntegralElem k i hi) n)

/-- `y ∘ φ : k[y] → A[1/x]`. -/
noncomputable def betaInf : Polynomial k →+* Ax k := (phi1 k i hi).comp (betaA k)

/-- **`y ∘ φ` is finite over `𝔸¹_y`.** -/
theorem betaInf_isIntegral : (betaInf k i hi).IsIntegral :=
  RingHom.IsIntegral.trans _ _ (betaA_isIntegral k) (phi1_isIntegral k i hi)

/-- `t = 1/z ↦ 0`: `A[1/x][t] → A[1/x]`. -/
noncomputable def piInf : Polynomial (Ax k) →+* Ax k := Polynomial.evalRingHom 0

omit [CharP k 3] hi in
theorem piInf_surjective : Function.Surjective (piInf k) := fun a => ⟨C a, by simp [piInf]⟩

/-- **The pinched chart `Spec(k[y] ×_{A[1/x]} A[1/x][t])` of `E × {∞}` along `y ∘ φ` is the
pushout of `Spec k[y] ← Spec A[1/x] → Spec A[1/x][t]` in `Scheme`.** -/
theorem isPushout_inf :
    IsPushout (Spec.map (CommRingCat.ofHom (piInf k)))
      (Spec.map (CommRingCat.ofHom (betaInf k i hi)))
      (Spec.map (CommRingCat.ofHom (FerrandPushout.pr₂ (piInf k) (betaInf k i hi))))
      (Spec.map (CommRingCat.ofHom (FerrandPushout.pr₁ (piInf k) (betaInf k i hi)))) :=
  FerrandPushout.isPushout (piInf_surjective k) (betaInf_isIntegral k i hi)

end Pcf.Examples.PaperP.MonodromyLossPinch

#print axioms Pcf.Examples.PaperP.MonodromyLossPinch.phi1_isIntegral
#print axioms Pcf.Examples.PaperP.MonodromyLossPinch.betaInf_isIntegral
#print axioms Pcf.Examples.PaperP.MonodromyLossPinch.isPushout_inf
