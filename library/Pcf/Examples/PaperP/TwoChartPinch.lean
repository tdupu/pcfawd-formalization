/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPinchDominant

/-!
# Pinching `Z × 𝔸¹` along `Z × {0}` and a map `Z → ℙ¹`, from two affine charts

For `paper-p.tex`, Example `ex:monodromy-loss`: the half `X₀` of the pinched variety was built in
`MonodromyLossPinchGlue` from the two charts `U_A`, `U_B` of `E`. The other half `X∞` needs the
same construction over a different pair of charts of `E` (saturated for `y ∘ φ`). This file does
the construction once, for any two-chart model of the curve:

`D : PinchData k Z0 Z1 Z01` is a curve `Ep = Spec Z0 ∪ Spec Z1` (glued along `Spec Z01`, with
`Z0 → Z01`, `Z1 → Z01` the localizations away from `e0`, `e1`), and a map `Ep → ℙ¹` given by
`β0 : k[u,v]_{(v)} → Z0`, `β1 : k[u,v]_{(u)} → Z1`, `β01 : k[u,v]_{(uv)} → Z01`, with
`β0 (u/v) = e0`, `β1 (v/u) = e1`.

* `Ep`, `EA` (`= Ep × 𝔸¹`), `Xp` (the pinching), `nu : EA ⟶ Xp`, `o : ℙ¹ ⟶ Xp`,
  `i : Ep ⟶ EA` (zero section), `yM : Ep ⟶ ℙ¹`, `comm : i ≫ nu = yM ≫ o`;
* `isPushout` (for `β0`, `β1` integral, `β0`, `β1` injective, `Z0`, `Z1` reduced):
  `Xp` is the pushout of `EA ← Ep → ℙ¹` in `Scheme`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.TwoChartPinch

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout Pcf.Examples.PaperP.MonodromyLossPinchGlue
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k]

local notation "uu" => (MvPolynomial.X (Sum.inl 0) : Coordinates k)
local notation "vv" => (MvPolynomial.X (Sum.inr ()) : Coordinates k)
local notation "P1" => Proj (grading k)

/-- A two-chart curve with a map to `ℙ¹`, chartwise on the standard charts. -/
structure PinchData (Z0 Z1 Z01 : Type u) [CommRing Z0] [CommRing Z1] [CommRing Z01] where
  z0 : Z0 →+* Z01
  z1 : Z1 →+* Z01
  e0 : Z0
  e1 : Z1
  loc0 : letI := z0.toAlgebra; IsLocalization.Away e0 Z01
  loc1 : letI := z1.toAlgebra; IsLocalization.Away e1 Z01
  β0 : Away (grading k) vv →+* Z0
  β1 : Away (grading k) uu →+* Z1
  β01 : Away (grading k) (uu * vv) →+* Z01
  hβ0 : β01.comp (g0 k) = z0.comp β0
  hβ1 : β01.comp (g1 k) = z1.comp β1
  β0_t0 : β0 (t0 k) = e0
  β1_t1 : β1 (t1 k) = e1

namespace PinchData

variable {k} {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
  (D : PinchData k Z0 Z1 Z01)

/-! ### Rings -/

/-- `z ↦ 0`. -/
noncomputable abbrev pi0 : Polynomial Z0 →+* Z0 := Polynomial.evalRingHom 0
noncomputable abbrev pi1 : Polynomial Z1 →+* Z1 := Polynomial.evalRingHom 0
noncomputable abbrev pi01 : Polynomial Z01 →+* Z01 := Polynomial.evalRingHom 0

/-- `Z0[z] → Z01[z]`, `Z1[z] → Z01[z]`. -/
noncomputable def q0 : Polynomial Z0 →+* Polynomial Z01 := Polynomial.mapRingHom D.z0
noncomputable def q1 : Polynomial Z1 →+* Polynomial Z01 := Polynomial.mapRingHom D.z1

theorem hπ0 : pi01.comp D.q0 = D.z0.comp pi0 := by ext <;> simp [q0]
theorem hπ1 : pi01.comp D.q1 = D.z1.comp pi1 := by ext <;> simp [q1]

/-- The pinched chart rings and their overlap. -/
abbrev R0 := Fib (pi0 (Z0 := Z0)) D.β0
abbrev R1 := Fib (pi1 (Z1 := Z1)) D.β1
abbrev R01 := Fib (pi01 (Z01 := Z01)) D.β01

noncomputable def f0 : D.R0 →+* D.R01 := fibMap _ _ _ _ D.q0 D.z0 (g0 k) D.hπ0 D.hβ0
noncomputable def f1 : D.R1 →+* D.R01 := fibMap _ _ _ _ D.q1 D.z1 (g1 k) D.hπ1 D.hβ1

noncomputable def h0 : D.R0 := ⟨(t0 k, Polynomial.C D.e0), by
  rw [mem_fib]; change D.β0 (t0 k) = pi0 (Polynomial.C D.e0); simp [D.β0_t0]⟩
noncomputable def h1 : D.R1 := ⟨(t1 k, Polynomial.C D.e1), by
  rw [mem_fib]; change D.β1 (t1 k) = pi1 (Polynomial.C D.e1); simp [D.β1_t1]⟩

theorem isLocalization_q0 :
    letI := D.q0.toAlgebra
    IsLocalization.Away (Polynomial.C D.e0) (Polynomial Z01) :=
  poly_away D.z0 D.e0 D.loc0

theorem isLocalization_q1 :
    letI := D.q1.toAlgebra
    IsLocalization.Away (Polynomial.C D.e1) (Polynomial Z01) :=
  poly_away D.z1 D.e1 D.loc1

theorem isLocalization_f0 :
    letI := D.f0.toAlgebra
    IsLocalization.Away D.h0 D.R01 := by
  letI := D.q0.toAlgebra
  letI := (g0 k).toAlgebra
  letI := D.z0.toAlgebra
  haveI : IsLocalization.Away (pr₂ pi0 D.β0 D.h0) (Polynomial Z01) := D.isLocalization_q0
  haveI : IsLocalization.Away (hbar pi0 D.β0 D.h0) Z01 := by
    change IsLocalization.Away (D.β0 (t0 k)) Z01
    rw [D.β0_t0]; exact D.loc0
  haveI : IsLocalization.Away (pr₁ pi0 D.β0 D.h0) (Away (grading k) (uu * vv)) :=
    isLocalization_g0 k
  exact isLocalization_fibMap D.h0 pi01 D.β01 D.hπ0 D.hβ0

theorem isLocalization_f1 :
    letI := D.f1.toAlgebra
    IsLocalization.Away D.h1 D.R01 := by
  letI := D.q1.toAlgebra
  letI := (g1 k).toAlgebra
  letI := D.z1.toAlgebra
  haveI : IsLocalization.Away (pr₂ pi1 D.β1 D.h1) (Polynomial Z01) := D.isLocalization_q1
  haveI : IsLocalization.Away (hbar pi1 D.β1 D.h1) Z01 := by
    change IsLocalization.Away (D.β1 (t1 k)) Z01
    rw [D.β1_t1]; exact D.loc1
  haveI : IsLocalization.Away (pr₁ pi1 D.β1 D.h1) (Away (grading k) (uu * vv)) :=
    isLocalization_g1 k
  exact isLocalization_fibMap D.h1 pi01 D.β01 D.hπ1 D.hβ1

instance f0_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.f0)) := by
  letI := D.f0.toAlgebra
  haveI := D.isLocalization_f0
  exact IsOpenImmersion.of_isLocalization (R := D.R0) (S := D.R01) D.h0

instance f1_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.f1)) := by
  letI := D.f1.toAlgebra
  haveI := D.isLocalization_f1
  exact IsOpenImmersion.of_isLocalization (R := D.R1) (S := D.R01) D.h1

instance q0_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.q0)) := by
  letI := D.q0.toAlgebra
  haveI := D.isLocalization_q0
  exact IsOpenImmersion.of_isLocalization (R := Polynomial Z0) (Polynomial.C D.e0)

instance q1_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.q1)) := by
  letI := D.q1.toAlgebra
  haveI := D.isLocalization_q1
  exact IsOpenImmersion.of_isLocalization (R := Polynomial Z1) (Polynomial.C D.e1)

instance z0_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.z0)) := by
  letI := D.z0.toAlgebra
  haveI := D.loc0
  exact IsOpenImmersion.of_isLocalization (R := Z0) (S := Z01) D.e0

instance z1_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.z1)) := by
  letI := D.z1.toAlgebra
  haveI := D.loc1
  exact IsOpenImmersion.of_isLocalization (R := Z1) (S := Z01) D.e1

/-! ### The glued schemes and maps -/

/-- The curve. -/
noncomputable def Ep : Scheme.{u} := TwoChartGlue.glued D.z0 D.z1
/-- The curve times `𝔸¹`. -/
noncomputable def EA : Scheme.{u} := TwoChartGlue.glued D.q0 D.q1
/-- The pinching. -/
noncomputable def Xp : Scheme.{u} := TwoChartGlue.glued D.f0 D.f1

/-- `ν : Ep × 𝔸¹ → Xp`. -/
noncomputable def nu : D.EA ⟶ D.Xp :=
  TwoChartGlue.desc D.q0 D.q1
    (Spec.map (CommRingCat.ofHom (pr₂ pi0 D.β0)) ≫ TwoChartGlue.ι₀ D.f0 D.f1)
    (Spec.map (CommRingCat.ofHom (pr₂ pi1 D.β1)) ≫ TwoChartGlue.ι₁ D.f0 D.f1) (by
      have e0 : (pr₂ pi01 D.β01).comp D.f0 = D.q0.comp (pr₂ pi0 D.β0) := rfl
      have e1 : (pr₂ pi01 D.β01).comp D.f1 = D.q1.comp (pr₂ pi1 D.β1) := rfl
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← e0,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, TwoChartGlue.compat,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1])

@[simp] theorem ι₀_nu : TwoChartGlue.ι₀ D.q0 D.q1 ≫ D.nu =
    Spec.map (CommRingCat.ofHom (pr₂ pi0 D.β0)) ≫ TwoChartGlue.ι₀ D.f0 D.f1 :=
  TwoChartGlue.ι₀_desc _ _ _ _ _

@[simp] theorem ι₁_nu : TwoChartGlue.ι₁ D.q0 D.q1 ≫ D.nu =
    Spec.map (CommRingCat.ofHom (pr₂ pi1 D.β1)) ≫ TwoChartGlue.ι₁ D.f0 D.f1 :=
  TwoChartGlue.ι₁_desc _ _ _ _ _

/-- `o : ℙ¹ → Xp`. -/
noncomputable def o : P1 ⟶ D.Xp :=
  P1desc k (Spec.map (CommRingCat.ofHom (pr₁ pi0 D.β0)) ≫ TwoChartGlue.ι₀ D.f0 D.f1)
    (Spec.map (CommRingCat.ofHom (pr₁ pi1 D.β1)) ≫ TwoChartGlue.ι₁ D.f0 D.f1) (by
      have e0 : (pr₁ pi01 D.β01).comp D.f0 = (g0 k).comp (pr₁ pi0 D.β0) := rfl
      have e1 : (pr₁ pi01 D.β01).comp D.f1 = (g1 k).comp (pr₁ pi1 D.β1) := rfl
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← e0,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, TwoChartGlue.compat,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1])

@[simp] theorem awayV_o : awayV k ≫ D.o =
    Spec.map (CommRingCat.ofHom (pr₁ pi0 D.β0)) ≫ TwoChartGlue.ι₀ D.f0 D.f1 :=
  awayV_P1desc k _ _ _

@[simp] theorem awayU_o : awayU k ≫ D.o =
    Spec.map (CommRingCat.ofHom (pr₁ pi1 D.β1)) ≫ TwoChartGlue.ι₁ D.f0 D.f1 :=
  awayU_P1desc k _ _ _

/-- `i : Ep → Ep × 𝔸¹`, the zero section. -/
noncomputable def i : D.Ep ⟶ D.EA :=
  TwoChartGlue.desc D.z0 D.z1
    (Spec.map (CommRingCat.ofHom pi0) ≫ TwoChartGlue.ι₀ D.q0 D.q1)
    (Spec.map (CommRingCat.ofHom pi1) ≫ TwoChartGlue.ι₁ D.q0 D.q1) (by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← D.hπ0,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, TwoChartGlue.compat,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, D.hπ1])

@[reassoc (attr := simp)] theorem ι₀_i : TwoChartGlue.ι₀ D.z0 D.z1 ≫ D.i =
    Spec.map (CommRingCat.ofHom pi0) ≫ TwoChartGlue.ι₀ D.q0 D.q1 :=
  TwoChartGlue.ι₀_desc _ _ _ _ _

@[reassoc (attr := simp)] theorem ι₁_i : TwoChartGlue.ι₁ D.z0 D.z1 ≫ D.i =
    Spec.map (CommRingCat.ofHom pi1) ≫ TwoChartGlue.ι₁ D.q0 D.q1 :=
  TwoChartGlue.ι₁_desc _ _ _ _ _

/-- The map `Ep → ℙ¹`. -/
noncomputable def yM : D.Ep ⟶ P1 :=
  TwoChartGlue.desc D.z0 D.z1 (Spec.map (CommRingCat.ofHom D.β0) ≫ awayV k)
    (Spec.map (CommRingCat.ofHom D.β1) ≫ awayU k) (by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← D.hβ0,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, g0_awayV,
        ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.hβ1,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc])

@[reassoc (attr := simp)] theorem ι₀_yM : TwoChartGlue.ι₀ D.z0 D.z1 ≫ D.yM =
    Spec.map (CommRingCat.ofHom D.β0) ≫ awayV k :=
  TwoChartGlue.ι₀_desc _ _ _ _ _

@[reassoc (attr := simp)] theorem ι₁_yM : TwoChartGlue.ι₁ D.z0 D.z1 ≫ D.yM =
    Spec.map (CommRingCat.ofHom D.β1) ≫ awayU k :=
  TwoChartGlue.ι₁_desc _ _ _ _ _

/-- **The pinching square commutes.** -/
theorem comm : D.i ≫ D.nu = D.yM ≫ D.o := by
  refine TwoChartGlue.hom_ext D.z0 D.z1 ?_ ?_
  · rw [ι₀_i_assoc, ι₀_yM_assoc, ι₀_nu, awayV_o,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← pr_comm]
  · rw [ι₁_i_assoc, ι₁_yM_assoc, ι₁_nu, awayU_o,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← pr_comm]

#print axioms isLocalization_f0
#print axioms comm

end PinchData

end Pcf.Examples.PaperP.TwoChartPinch
