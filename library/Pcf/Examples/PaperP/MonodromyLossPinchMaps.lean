/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPinchGlue

/-!
# The pinching square near `E × {0}`

For `paper-p.tex`, Example `ex:monodromy-loss`: the square

    E ──i₀──> E × 𝔸¹
    │y           │ν₀
    v            v
    ℙ¹ ──o₀───> X₀

* `P1desc`: morphisms out of `ℙ¹ = Proj k[u,v]` from compatible maps on `D₊(u)`, `D₊(v)`;
* `o0 : ℙ¹ → X₀`, chartwise `Spec k[u,v]_{(v)} → Spec R0`, `Spec k[u,v]_{(u)} → Spec R1`;
* `i0 : E → E × 𝔸¹`, the zero section `z = 0`;
* **`comm0`**: `i₀ ≫ ν₀ = y ≫ o₀`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossPinchGlue

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k]

local notation "uu" => (MvPolynomial.X (Sum.inl 0) : Coordinates k)
local notation "vv" => (MvPolynomial.X (Sum.inr ()) : Coordinates k)
local notation "P1" => Proj (grading k)

/-- `D₊(v) ⊆ ℙ¹`. -/
noncomputable abbrev awayV : Spec (.of (Away (grading k) vv)) ⟶ P1 :=
  Proj.awayι (grading k) vv (vv_mem k) Nat.zero_lt_one
/-- `D₊(u) ⊆ ℙ¹`. -/
noncomputable abbrev awayU : Spec (.of (Away (grading k) uu)) ⟶ P1 :=
  Proj.awayι (grading k) uu (uu_mem k) Nat.zero_lt_one

/-- The chart family on `P1Cover`. -/
noncomputable def P1family {T : Scheme.{u}} (av : Spec (.of (Away (grading k) vv)) ⟶ T)
    (au : Spec (.of (Away (grading k) uu)) ⟶ T) : ∀ i : Index, (P1Cover k).X i ⟶ T
  | Sum.inl i => by obtain rfl : i = 0 := Subsingleton.elim _ _; exact au
  | Sum.inr () => av

/-- **Morphisms out of `ℙ¹`** from compatible maps on the two standard charts. -/
noncomputable def P1desc {T : Scheme.{u}} (av : Spec (.of (Away (grading k) vv)) ⟶ T)
    (au : Spec (.of (Away (grading k) uu)) ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (g0 k)) ≫ av = Spec.map (CommRingCat.ofHom (g1 k)) ≫ au) :
    P1 ⟶ T :=
  (P1Cover k).glueMorphisms (P1family k av au) (by
    rintro (i | ⟨⟩) (j | ⟨⟩)
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact congrArg (· ≫ au) (fst_eq_snd_of_mono_eq (f := awayU k))
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      change pullback.fst (awayU k) (awayV k) ≫ au = pullback.snd (awayU k) (awayV k) ≫ av
      rw [← cancel_epi (Proj.pullbackAwayιIso (grading k) (uu_mem k) Nat.zero_lt_one (vv_mem k)
        Nat.zero_lt_one (x := uu * vv) rfl).inv, Proj.pullbackAwayιIso_inv_fst_assoc,
        Proj.pullbackAwayιIso_inv_snd_assoc]
      exact h.symm
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      change pullback.fst (awayV k) (awayU k) ≫ av = pullback.snd (awayV k) (awayU k) ≫ au
      rw [← cancel_epi (Proj.pullbackAwayιIso (grading k) (vv_mem k) Nat.zero_lt_one (uu_mem k)
        Nat.zero_lt_one (x := uu * vv) (mul_comm _ _)).inv, Proj.pullbackAwayιIso_inv_fst_assoc,
        Proj.pullbackAwayιIso_inv_snd_assoc]
      exact h
    · exact congrArg (· ≫ av) (fst_eq_snd_of_mono_eq (f := awayV k)))

@[simp] theorem awayV_P1desc {T : Scheme.{u}} (av : Spec (.of (Away (grading k) vv)) ⟶ T)
    (au : Spec (.of (Away (grading k) uu)) ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (g0 k)) ≫ av = Spec.map (CommRingCat.ofHom (g1 k)) ≫ au) :
    awayV k ≫ P1desc k av au h = av :=
  (P1Cover k).ι_glueMorphisms (P1family k av au) _ (Sum.inr ())

@[simp] theorem awayU_P1desc {T : Scheme.{u}} (av : Spec (.of (Away (grading k) vv)) ⟶ T)
    (au : Spec (.of (Away (grading k) uu)) ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (g0 k)) ≫ av = Spec.map (CommRingCat.ofHom (g1 k)) ≫ au) :
    awayU k ≫ P1desc k av au h = au :=
  (P1Cover k).ι_glueMorphisms (P1family k av au) _ (Sum.inl 0)

theorem P1_hom_ext {T : Scheme.{u}} {a b : P1 ⟶ T} (hv : awayV k ≫ a = awayV k ≫ b)
    (hu : awayU k ≫ a = awayU k ≫ b) : a = b :=
  (P1Cover k).hom_ext _ _ (by
    rintro (i | ⟨⟩)
    · obtain rfl : i = 0 := Subsingleton.elim _ _; exact hu
    · exact hv)

/-! ### The maps `o₀` and `i₀` -/

/-- `o₀ : ℙ¹ → X₀`. -/
noncomputable def o0 : P1 ⟶ X0 k :=
  P1desc k (Spec.map (CommRingCat.ofHom (pr₁ (piA k) (beta0 k))) ≫ TwoChartGlue.ι₀ (f0 k) (f1 k))
    (Spec.map (CommRingCat.ofHom (pr₁ (piB k) (beta1 k))) ≫ TwoChartGlue.ι₁ (f0 k) (f1 k)) (by
      have e0 : (pr₁ (pi01 k) (beta01 k)).comp (f0 k) = (g0 k).comp (pr₁ (piA k) (beta0 k)) :=
        rfl
      have e1 : (pr₁ (pi01 k) (beta01 k)).comp (f1 k) = (g1 k).comp (pr₁ (piB k) (beta1 k)) :=
        rfl
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← e0,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, TwoChartGlue.compat,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1])

@[simp] theorem awayV_o0 : awayV k ≫ o0 k =
    Spec.map (CommRingCat.ofHom (pr₁ (piA k) (beta0 k))) ≫ TwoChartGlue.ι₀ (f0 k) (f1 k) :=
  awayV_P1desc k _ _ _

@[simp] theorem awayU_o0 : awayU k ≫ o0 k =
    Spec.map (CommRingCat.ofHom (pr₁ (piB k) (beta1 k))) ≫ TwoChartGlue.ι₁ (f0 k) (f1 k) :=
  awayU_P1desc k _ _ _

/-- `i₀ : E → E × 𝔸¹`, `P ↦ (P, 0)`. -/
noncomputable def i0 : E k ⟶ EA1 k :=
  desc k (Spec.map (CommRingCat.ofHom (piA k)) ≫ TwoChartGlue.ι₀ (p0 k) (p1 k))
    (Spec.map (CommRingCat.ofHom (piB k)) ≫ TwoChartGlue.ι₁ (p0 k) (p1 k)) (by
      have e0 : (algebraMap (A k) (Ay k)).comp (piA k) = (pi01 k).comp (p0 k) := (hπ0 k).symm
      have e1 : (BtoAy k).comp (piB k) = (pi01 k).comp (p1 k) := (hπ1 k).symm
      rw [jA, jB, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e0,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, TwoChartGlue.compat,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1])

@[reassoc (attr := simp)] theorem ιA_i0 : ιA k ≫ i0 k =
    Spec.map (CommRingCat.ofHom (piA k)) ≫ TwoChartGlue.ι₀ (p0 k) (p1 k) := ιA_desc k _ _ _

@[reassoc (attr := simp)] theorem ιB_i0 : ιB k ≫ i0 k =
    Spec.map (CommRingCat.ofHom (piB k)) ≫ TwoChartGlue.ι₁ (p0 k) (p1 k) := ιB_desc k _ _ _

/-- **The pinching square commutes**: `i₀ ≫ ν₀ = y ≫ o₀`. -/
theorem comm0 : i0 k ≫ nu0 k = yMap k ≫ o0 k := by
  refine hom_ext k ?_ ?_
  · rw [ιA_i0_assoc, ← Category.assoc (ιA k), ιA_yMap, ι₀_nu0, yChartA, Category.assoc, awayV_o0,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← pr_comm]
    rfl
  · rw [ιB_i0_assoc, ← Category.assoc (ιB k), ιB_yMap, ι₁_nu0, yChartB, Category.assoc, awayU_o0,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← pr_comm]
    rfl

#print axioms P1desc
#print axioms o0
#print axioms i0
#print axioms comm0

end Pcf.Examples.PaperP.MonodromyLossPinchGlue
