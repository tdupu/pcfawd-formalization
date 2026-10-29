/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalFinite
public import Pcf.Examples.PaperP.NormalizationOfBirationalCover

/-!
# `ν : E ×ₖ ℙ¹ → X` is birational (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868). `ν` is an open immersion on
`E × 𝔾ₘ` (`TwoChartPinchUnits.wX_isOpenImmersion`), which contains the generic point of
`E ×ₖ ℙ¹`.

* `cW : E × 𝔾ₘ ⟶ E ×ₖ ℙ¹`, `cW_nu`: `cW ≫ ν` is an open immersion;
* `W0_nonempty`, `genericPoint_mem_range_cW`;
* **`nu_stalkMap_genericPoint_isIso`**, **`nu_birational`**: `Spec K(E ×ₖ ℙ¹) ≅ Spec K(X)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossPinchGlue
open BasilicaProjectiveScheme (grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `E × 𝔾ₘ ⟶ E ×ₖ ℙ¹`. -/
noncomputable def cW : (D0 k).W.toScheme ⟶ EP1 k := (D0 k).W.ι ≫ c0 k

instance cW_isOpenImmersion : IsOpenImmersion (cW k) := by unfold cW; infer_instance

theorem cW_nu : cW k ≫ nu k i hi = (D0 k).wX ≫ j0 k i hi := by
  rw [cW, Category.assoc, c0_nu, PinchData.wX, Category.assoc]

instance cW_nu_isOpenImmersion : IsOpenImmersion (cW k ≫ nu k i hi) := by
  rw [cW_nu]; infer_instance

omit [CharP k 3] in
theorem W0_nonempty : Nonempty (D0 k).W := by
  have hp : (⊥ : Ideal (Polynomial (A k))).IsPrime := Ideal.isPrime_bot
  let a : Spec (.of (Polynomial (A k))) := ⟨⊥, hp⟩
  refine ⟨⟨TwoChartGlue.ι₀ (D0 k).q0 (D0 k).q1 a, ?_⟩⟩
  rw [PinchData.mem_W_ι₀]
  change (Polynomial.X : Polynomial (A k)) ∉ (⊥ : Ideal (Polynomial (A k)))
  rw [Ideal.mem_bot]
  exact Polynomial.X_ne_zero

omit [CharP k 3] in
theorem genericPoint_mem_range_cW : genericPoint (EP1 k) ∈ Set.range (cW k) := by
  rw [(genericPoint_spec (EP1 k)).mem_open_set_iff (cW k).isOpenEmbedding.isOpen_range]
  obtain ⟨w⟩ := W0_nonempty k
  exact ⟨cW k w, trivial, w, rfl⟩

/-- **`ν` is an isomorphism at the generic point.** -/
instance nu_stalkMap_genericPoint_isIso : IsIso ((nu k i hi).stalkMap (genericPoint (EP1 k))) := by
  obtain ⟨w, hw⟩ := genericPoint_mem_range_cW k
  rw [← hw]
  exact NormalizationOfBirationalCover.isIso_stalkMap_of_comp (cW k) (nu k i hi) w

instance nu_isDominant : IsDominant (nu k i hi) := inferInstance

/-- **`ν` is birational.** -/
instance nu_birational : IsIso (Pcf.schemeGenericMorphism (nu k i hi)) :=
  NormalizationOfBirationalCover.schemeGenericMorphism_isIso_of_stalkMap _

#print axioms nu_birational

end Pcf.Examples.PaperP.MonodromyLossGlobal
