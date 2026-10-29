/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalNormalization

/-!
# The pinched `X` of `ex:monodromy-loss` is not normal

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): "the resulting nonnormal variety `X`".

The points `P₀ = (0, 0)` and `P₁ = (1, 0)` of `E : y² = x³ - x` are distinct with `y(P₀) = y(P₁)`,
so `(P₀, 0) ≠ (P₁, 0)` in `E ×ₖ ℙ¹` have the same image under `ν` (`E × {0}` is pinched along
`y`). Hence `ν` is not injective, so not an isomorphism; if `X` were normal its normalization map
would be an isomorphism, and so would `ν`.

* `evA`, `pt`: the `k`-points `(a, 0)` of `Spec A` for `a³ = a`;
* `pt0_ne_pt1`, `yChartA_pt`: distinct with the same `y`;
* **`nu_not_injective`**;
* **`X_not_isNormalScheme`**.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductSlices
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

omit [CharP k 3] in
/-- Evaluation at `(a, 0)`. -/
noncomputable def evA (a : k) (h : (0 : k) ^ 2 = a ^ 3 - a) : A k →ₐ[k] k :=
  { liftA k a 0 h with
    commutes' := fun c => by
      change liftA k a 0 h (AdjoinRoot.of _ (Polynomial.C c)) = c
      simp [liftA] }

omit [CharP k 3] in
theorem evA_x (a : k) (h : (0 : k) ^ 2 = a ^ 3 - a) : evA k a h (xA k) = a := liftA_x k _ _ h

omit [CharP k 3] in
theorem evA_y (a : k) (h : (0 : k) ^ 2 = a ^ 3 - a) : evA k a h (yA k) = 0 := liftA_y k _ _ h

omit [CharP k 3] in
/-- The point `(a, 0)` of `Spec A`. -/
noncomputable def pt (a : k) (h : (0 : k) ^ 2 = a ^ 3 - a) : Spec (.of (A k)) :=
  ⟨RingHom.ker (evA k a h).toRingHom, RingHom.ker_isPrime _⟩

omit [CharP k 3] in
theorem h0 : (0 : k) ^ 2 = 0 ^ 3 - 0 := by ring
omit [CharP k 3] in
theorem h1 : (0 : k) ^ 2 = 1 ^ 3 - 1 := by ring

omit [CharP k 3] in
theorem pt0_ne_pt1 : pt k 0 (h0 k) ≠ pt k 1 (h1 k) := by
  intro h
  have hx : xA k ∈ (pt k 0 (h0 k)).asIdeal := by
    change (evA k 0 (h0 k)).toRingHom (xA k) = 0
    exact evA_x k _ _
  rw [h] at hx
  change (evA k 1 (h1 k)).toRingHom (xA k) = 0 at hx
  have : (evA k 1 (h1 k)) (xA k) = 1 := evA_x k _ _
  exact one_ne_zero (this.symm.trans hx)

omit [CharP k 3] in
theorem yChartA_pt : yChartA k (pt k 0 (h0 k)) = yChartA k (pt k 1 (h1 k)) := by
  rw [yChartA, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap _ (RingHom.ker _) = Ideal.comap _ (RingHom.ker _)
  rw [RingHom.comap_ker, RingHom.comap_ker]
  have e (a : k) (h : (0 : k) ^ 2 = a ^ 3 - a) :
      (evA k a h).toRingHom.comp (awayEval _ (valsA k) (valsA_v k)) =
        awayEval _ (Sum.elim (fun _ => (0 : k)) (fun _ => 1)) (by simp) := by
    rw [AlgHom.toRingHom_eq_coe, awayEval_comp (evA k a h) _ _ _ (by
      simp [valsA])]
    congr 1
    funext j
    rcases j with _ | _ <;> simp [valsA, evA_y]
  exact (congrArg RingHom.ker (e 0 (h0 k))).trans (congrArg RingHom.ker (e 1 (h1 k))).symm

/-- `ν` on `E × {0}` factors through `y` (the first pinching). -/
theorem slice0_nu : slice0 k ≫ nu k i hi = yMap k ≫ coprod.inl ≫ oX k i hi := by
  have h := coprod.inl ≫= w k i hi
  simpa [iZ, jZ] using h

/-- **`ν` is not injective:** `(P₀, 0)` and `(P₁, 0)` have the same image. -/
theorem nu_not_injective : ¬ Function.Injective (nu k i hi) := by
  intro hinj
  have key (e : E k) : nu k i hi (slice0 k e) =
      (coprod.inl ≫ oX k i hi : Proj (grading k) ⟶ X k i hi) (yMap k e) := by
    rw [← Scheme.Hom.comp_apply, slice0_nu]; rfl
  have hfst (e : E k) :
      pullback.fst (toSpec k) (BasilicaProjectiveScheme.structureMap k) (slice0 k e) = e := by
    rw [← Scheme.Hom.comp_apply, slice_fst]; rfl
  have hyA (p : Spec (.of (A k))) : yMap k (ιA k p) = yChartA k p := by
    rw [← Scheme.Hom.comp_apply, ιA_yMap]
  have hy : yMap k (ιA k (pt k 0 (h0 k))) = yMap k (ιA k (pt k 1 (h1 k))) := by
    rw [hyA, hyA, yChartA_pt]
  have hs := hinj ((key _).trans ((congrArg _ (congrArg _ hy)).trans (key _).symm))
  have he := (hfst _).symm.trans ((congrArg _ hs).trans (hfst _))
  exact pt0_ne_pt1 k ((ιA k).isOpenEmbedding.injective he)

/-- **`X` is not normal** (`ex:monodromy-loss`: "the resulting nonnormal variety `X`").

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem X_not_isNormalScheme : ¬ Pcf.IsNormalScheme (X k i hi) := by
  intro hX
  haveI := Pcf.normalScheme_normalizationMap_isIso (X k i hi)
  haveI : IsIso (nu k i hi) := by
    rw [← normalizationIso_inv_normalizationMap]; infer_instance
  exact nu_not_injective k i hi (nu k i hi).isOpenEmbedding.injective

#print axioms nu_not_injective
#print axioms X_not_isNormalScheme

end Pcf.Examples.PaperP.MonodromyLossGlobal
