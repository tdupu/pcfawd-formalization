/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossInfCharts

/-!
# `X∞` is the pushout of `E' × 𝔸¹ ← E' → ℙ¹` (pinching of `E × {∞}` along `y ∘ φ`)

For `paper-p.tex`, Example `ex:monodromy-loss`. With `infData` from `MonodromyLossInfCharts`:

* `psiA_finite`, `psiA_injective`, `psiInf_injective`: `A → Γ(φ⁻¹ U_A)` and
  `B → Γ(φ⁻¹ U_B)` are finite and injective (`φ` is finite and scheme-theoretically dominant,
  and the charts are flat base changes);
* `infβ0_isIntegral`, `infβ1_isIntegral`, `infβ0_injective`, `infβ1_injective`;
* `VInf`, `UInf` reduced;
* **`isPushoutInf`**: `XInf = infData.Xp` is the pushout of
  `infData.EA ←i infData.Ep →(y ∘ φ) ℙ¹` in `Scheme`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossInf

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout Pcf.Examples.PaperP.MonodromyLossPinchGlue
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossThirdChart
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

theorem psi_finite {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R) [IsFinite g] :
    (psi g).Finite := by
  have h1 := Scheme.Hom.finite_appTop g
  have h2 : (Scheme.ΓSpecIso R).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2
  exact h1.comp h2

theorem psi_injective {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R)
    [IsSchemeTheoreticallyDominant g] [QuasiCompact g] : Function.Injective (psi g) :=
  (g.app_injective ⊤).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1

instance phi_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (phi k i hi) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

theorem psiA_finite : (psiA k i hi).Finite := psi_finite _
theorem psiA_injective : Function.Injective (psiA k i hi) := psi_injective _
theorem psiInf_injective : Function.Injective (psiInf k i hi) := psi_injective _

theorem infβ0_isIntegral : (infData k i hi).β0.IsIntegral :=
  ((psiA_finite k i hi).comp (awayEval_v_finite k)).to_isIntegral

theorem infβ1_isIntegral : (infData k i hi).β1.IsIntegral :=
  ((psiInf_finite k i hi).comp (awayEval_u_finite k)).to_isIntegral

theorem infβ0_injective : Function.Injective (infData k i hi).β0 :=
  (psiA_injective k i hi).comp (beta0_injective k)

theorem infβ1_injective : Function.Injective (infData k i hi).β1 :=
  (psiInf_injective k i hi).comp (beta1_injective k)

instance VInf_isReduced : AlgebraicGeometry.IsReduced (VInf k i hi) :=
  isReduced_of_isOpenImmersion (pullback.fst (phi k i hi) (ιA k))

instance UInf_isReduced : AlgebraicGeometry.IsReduced (UInf k i hi) :=
  isReduced_of_isOpenImmersion (pullback.fst (phi k i hi) (ιB k))

/-- The pinching `X∞` of `E' × 𝔸¹_t` along `E' × {t = 0}` and `y ∘ φ`. -/
noncomputable abbrev XInf : Scheme.{u} := (infData k i hi).Xp

/-- **`X∞` is the pushout of `E' × 𝔸¹ ←i E' →(y ∘ φ) ℙ¹` in `Scheme`.** -/
theorem isPushoutInf :
    IsPushout (infData k i hi).i (infData k i hi).yM (infData k i hi).nu (infData k i hi).o :=
  (infData k i hi).isPushout (infβ0_isIntegral k i hi) (infβ1_isIntegral k i hi)
    (infβ0_injective k i hi) (infβ1_injective k i hi)

#print axioms psiA_injective
#print axioms isPushoutInf

end Pcf.Examples.PaperP.MonodromyLossInf
