/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossYFinite
public import Pcf.Examples.PaperP.FerrandPushoutMap
public import Pcf.Examples.PaperP.TwoChartGlue

/-!
# The pinching `X₀` of `E × 𝔸¹` along `E × {0}` and `y` (ring level and gluing)

For `paper-p.tex`, Example `ex:monodromy-loss`: "Pinch `E × {0}` along `y : E → ℙ¹`". Near
`E × {0}` the pinched variety `X₀` has two affine charts, lying over the two standard charts
`D₊(v)`, `D₊(u)` of `ℙ¹ = Proj k[u,v]` (the model of `MonodromyLossYMap`):

* `R0 = k[u,v]_{(v)} ×_A A[z]` (pinching `U_A × 𝔸¹` along `y = u/v : U_A → D₊(v)`);
* `R1 = k[u,v]_{(u)} ×_B B[z]` (pinching `U_B × 𝔸¹` along `w = v/u : U_B → D₊(u)`);
* the overlap `R01 = k[u,v]_{(uv)} ×_{A[1/y]} A[1/y][z]`.

`f0 : R0 → R01` and `f1 : R1 → R01` are localizations away from `h0 = (u/v, y)` and
`h1 = (v/u, w)` (`isLocalization_f0`, `isLocalization_f1`, via
`FerrandPushout.isLocalization_fibMap`), so their spectra are open immersions and the charts glue
(`X0 = TwoChartGlue.glued f0 f1`). The unpinched product `E × 𝔸¹` is glued the same way from
`A[z]`, `B[z]` along `A[1/y][z]` (`EA1`).
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

/-! ### Polynomial rings over localizations -/

section Poly

variable {R S : Type u} [CommRing R] [CommRing S]

/-- If `S` is `R` localized away from `r` (via `f`), then `S[z]` is `R[z]` localized away from
`C r` (via `map f`). -/
theorem poly_away (f : R →+* S) (r : R)
    (H : letI := f.toAlgebra; IsLocalization.Away r S) :
    letI := (Polynomial.mapRingHom f).toAlgebra
    IsLocalization.Away (Polynomial.C r) (Polynomial S) := by
  letI := f.toAlgebra
  letI := Polynomial.algebra R S
  have h := Polynomial.isLocalization (Submonoid.powers r) S
  rw [Submonoid.map_powers] at h
  have e : (Polynomial.mapRingHom f).toAlgebra = Polynomial.algebra R S :=
    Algebra.algebra_ext _ _ fun p => rfl
  rw [e]
  exact h

end Poly

variable (k : Type u) [Field k]

local notation "uu" => (MvPolynomial.X (Sum.inl 0) : Coordinates k)
local notation "vv" => (MvPolynomial.X (Sum.inr ()) : Coordinates k)

/-! ### The rings -/

/-- `y : U_A → D₊(v)` on rings. -/
noncomputable def beta0 : Away (grading k) vv →+* A k := awayEval vv (valsA k) (valsA_v k)
/-- `y : U_B → D₊(u)` on rings. -/
noncomputable def beta1 : Away (grading k) uu →+* B k := awayEval uu (valsB k) (valsB_u k)
/-- `y : U_A ∩ U_B → D₊(uv)` on rings. -/
noncomputable def beta01 : Away (grading k) (uu * vv) →+* Ay k :=
  awayEval (uu * vv) (valsAy k) (valsAy_uv k)
/-- `z ↦ 0` on the overlap. -/
noncomputable def pi01 : Polynomial (Ay k) →+* Ay k := Polynomial.evalRingHom 0

/-- The first pinched chart ring. -/
abbrev R0 := Fib (piA k) (beta0 k)
/-- The second pinched chart ring. -/
abbrev R1 := Fib (piB k) (beta1 k)
/-- The overlap ring. -/
abbrev R01 := Fib (pi01 k) (beta01 k)

/-- `D₊(uv) ⊆ D₊(v)`. -/
noncomputable def g0 : Away (grading k) vv →+* Away (grading k) (uu * vv) :=
  awayMap (grading k) (uu_mem k) (mul_comm uu vv)
/-- `D₊(uv) ⊆ D₊(u)`. -/
noncomputable def g1 : Away (grading k) uu →+* Away (grading k) (uu * vv) :=
  awayMap (grading k) (vv_mem k) rfl

/-- `A[z] → A[1/y][z]`. -/
noncomputable def p0 : Polynomial (A k) →+* Polynomial (Ay k) :=
  Polynomial.mapRingHom (algebraMap (A k) (Ay k))
/-- `B[z] → A[1/y][z]`. -/
noncomputable def p1 : Polynomial (B k) →+* Polynomial (Ay k) := Polynomial.mapRingHom (BtoAy k)

theorem hπ0 : (pi01 k).comp (p0 k) = (algebraMap (A k) (Ay k)).comp (piA k) := by
  ext <;> simp [pi01, p0, piA]

theorem hπ1 : (pi01 k).comp (p1 k) = (BtoAy k).comp (piB k) := by
  ext <;> simp [pi01, p1, piB]

theorem hβ0 : (beta01 k).comp (g0 k) = (algebraMap (A k) (Ay k)).comp (beta0 k) := by
  have e1 : (algebraMap (A k) (Ay k)).comp (awayEval vv (valsA k) (valsA_v k)) =
      awayEval vv (valsAy k) (valsAy_v k) := by
    have := awayEval_comp (IsScalarTower.toAlgHom k (A k) (Ay k)) vv (valsA k) (valsA_v k)
      (by convert valsAy_v k using 3; funext i; rcases i with _ | _ <;> simp [valsA, valsAy])
    refine this.trans ?_
    congr 1
    funext i; rcases i with _ | _ <;> simp [valsA, valsAy]
  have e2 := awayEval_awayMap (uu_mem k) (mul_comm uu vv) (valsAy k) (valsAy_uv k) (valsAy_v k)
  rw [beta01, g0, e2, beta0, e1]

theorem hβ1 : (beta01 k).comp (g1 k) = (BtoAy k).comp (beta1 k) := by
  have hB : IsUnit (MvPolynomial.aeval (fun i => BtoAyₐ k (valsB k i)) uu) := by simp [valsB]
  have e1 : (BtoAy k).comp (awayEval uu (valsB k) (valsB_u k)) =
      awayEval uu (valsAy k) (valsAy_u k) := by
    have := awayEval_comp (BtoAyₐ k) uu (valsB k) (valsB_u k) hB
    refine this.trans ?_
    rw [← awayEval_smul (MvPolynomial.isHomogeneous_X k (Sum.inl 0))
      (algebraMap (A k) (Ay k) (yA k))
      _ (by convert valsAy_u k using 3; funext i; rcases i with _ | _ <;>
        simp [valsB, valsAy, BtoAyₐ, BtoAy, liftB_w]) hB]
    congr 1
    funext i; rcases i with _ | _ <;> simp [valsB, valsAy, BtoAyₐ, BtoAy, liftB_w]
  have e2 := awayEval_awayMap (vv_mem k) (rfl : uu * vv = uu * vv) (valsAy k) (valsAy_uv k)
    (valsAy_u k)
  rw [beta01, g1, e2, beta1, e1]

/-- The chart maps `R0 → R01`, `R1 → R01`. -/
noncomputable def f0 : R0 k →+* R01 k :=
  fibMap _ _ _ _ (p0 k) (algebraMap (A k) (Ay k)) (g0 k) (hπ0 k) (hβ0 k)
noncomputable def f1 : R1 k →+* R01 k :=
  fibMap _ _ _ _ (p1 k) (BtoAy k) (g1 k) (hπ1 k) (hβ1 k)

/-! ### The localizing elements -/

/-- `u/v ∈ k[u,v]_{(v)}`. -/
noncomputable abbrev t0 : Away (grading k) vv := Away.isLocalizationElem (vv_mem k) (uu_mem k)
/-- `v/u ∈ k[u,v]_{(u)}`. -/
noncomputable abbrev t1 : Away (grading k) uu := Away.isLocalizationElem (uu_mem k) (vv_mem k)

theorem beta0_t0 : beta0 k (t0 k) = yA k := by
  have h := awayEval_mk_one k (vv_mem k) (uu ^ 1) (by simpa using uu_mem k) (valsA k)
    (valsA_v k)
  have h1 : MvPolynomial.aeval (valsA k) vv = 1 := by simp [valsA]
  have h2 : MvPolynomial.aeval (valsA k) (uu ^ 1) = yA k := by simp [valsA]
  rw [h1, h2, mul_one] at h
  exact h

theorem beta1_t1 : beta1 k (t1 k) = wB k := by
  have h := awayEval_mk_one k (uu_mem k) (vv ^ 1) (by simpa using vv_mem k) (valsB k)
    (valsB_u k)
  have h1 : MvPolynomial.aeval (valsB k) uu = 1 := by simp [valsB]
  have h2 : MvPolynomial.aeval (valsB k) (vv ^ 1) = wB k := by simp [valsB]
  rw [h1, h2, mul_one] at h
  exact h

/-- `h0 = (u/v, y) ∈ R0`. -/
noncomputable def h0 : R0 k := ⟨(t0 k, Polynomial.C (yA k)), by
  rw [mem_fib]; change beta0 k (t0 k) = piA k (Polynomial.C (yA k)); simp [beta0_t0, piA]⟩
/-- `h1 = (v/u, w) ∈ R1`. -/
noncomputable def h1 : R1 k := ⟨(t1 k, Polynomial.C (wB k)), by
  rw [mem_fib]; change beta1 k (t1 k) = piB k (Polynomial.C (wB k)); simp [beta1_t1, piB]⟩

theorem hbar_h0 : hbar _ _ (h0 k) = yA k := beta0_t0 k
theorem hbar_h1 : hbar _ _ (h1 k) = wB k := beta1_t1 k

/-! ### Localization structures -/

/-- `A[1/y]` is `B` localized away from `w`, via `BtoAy`. -/
theorem BtoAy_isLocalization :
    letI := (BtoAy k).toAlgebra
    IsLocalization.Away (wB k) (Ay k) := by
  letI := (BtoAy k).toAlgebra
  let e : Bw k ≃ₐ[B k] Ay k :=
    { RingEquiv.ofRingHom (BwToAy k) (AyToBw k) (BwToAy_comp_AyToBw k)
        (AyToBw_comp_BwToAy k) with
      commutes' := fun b => BwToAy_algebraMap k b }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (wB k)) e

theorem Ay_isLocalization :
    letI := (algebraMap (A k) (Ay k)).toAlgebra
    IsLocalization.Away (yA k) (Ay k) := by
  have e : (algebraMap (A k) (Ay k)).toAlgebra = (inferInstance : Algebra (A k) (Ay k)) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [e]
  infer_instance

/-- **`f0` is the localization of `R0` away from `h0`.** -/
theorem isLocalization_f0 :
    letI := (f0 k).toAlgebra
    IsLocalization.Away (h0 k) (R01 k) := by
  letI := (p0 k).toAlgebra
  letI := (g0 k).toAlgebra
  haveI : IsLocalization.Away (pr₂ (piA k) (beta0 k) (h0 k)) (Polynomial (Ay k)) :=
    poly_away (algebraMap (A k) (Ay k)) (yA k)
      (Ay_isLocalization k)
  haveI : IsLocalization.Away (hbar (piA k) (beta0 k) (h0 k)) (Ay k) := by
    rw [hbar_h0]; infer_instance
  haveI : IsLocalization.Away (pr₁ (piA k) (beta0 k) (h0 k)) (Away (grading k) (uu * vv)) :=
    Away.isLocalization_mul (vv_mem k) (uu_mem k) (mul_comm uu vv) one_ne_zero
  exact isLocalization_fibMap (h0 k) (pi01 k) (beta01 k) (hπ0 k) (hβ0 k)

/-- **`f1` is the localization of `R1` away from `h1`.** -/
theorem isLocalization_f1 :
    letI := (f1 k).toAlgebra
    IsLocalization.Away (h1 k) (R01 k) := by
  letI := (p1 k).toAlgebra
  letI := (g1 k).toAlgebra
  letI := (BtoAy k).toAlgebra
  haveI : IsLocalization.Away (pr₂ (piB k) (beta1 k) (h1 k)) (Polynomial (Ay k)) :=
    poly_away (BtoAy k) (wB k) (BtoAy_isLocalization k)
  haveI : IsLocalization.Away (hbar (piB k) (beta1 k) (h1 k)) (Ay k) := by
    rw [hbar_h1]; exact BtoAy_isLocalization k
  haveI : IsLocalization.Away (pr₁ (piB k) (beta1 k) (h1 k)) (Away (grading k) (uu * vv)) :=
    Away.isLocalization_mul (uu_mem k) (vv_mem k) rfl one_ne_zero
  exact isLocalization_fibMap (h1 k) (pi01 k) (beta01 k) (hπ1 k) (hβ1 k)

instance f0_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom (f0 k))) := by
  letI := (f0 k).toAlgebra
  haveI := isLocalization_f0 k
  exact IsOpenImmersion.of_isLocalization (R := R0 k) (S := R01 k) (h0 k)

instance f1_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom (f1 k))) := by
  letI := (f1 k).toAlgebra
  haveI := isLocalization_f1 k
  exact IsOpenImmersion.of_isLocalization (R := R1 k) (S := R01 k) (h1 k)

theorem isLocalization_p0 :
    letI := (p0 k).toAlgebra
    IsLocalization.Away (Polynomial.C (yA k)) (Polynomial (Ay k)) :=
  poly_away (algebraMap (A k) (Ay k)) (yA k)
    (Ay_isLocalization k)

theorem isLocalization_p1 :
    letI := (p1 k).toAlgebra
    IsLocalization.Away (Polynomial.C (wB k)) (Polynomial (Ay k)) :=
  poly_away (BtoAy k) (wB k) (BtoAy_isLocalization k)

instance p0_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom (p0 k))) := by
  letI := (p0 k).toAlgebra
  haveI := isLocalization_p0 k
  exact IsOpenImmersion.of_isLocalization (R := Polynomial (A k)) (Polynomial.C (yA k))

instance p1_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom (p1 k))) := by
  letI := (p1 k).toAlgebra
  haveI := isLocalization_p1 k
  exact IsOpenImmersion.of_isLocalization (R := Polynomial (B k)) (Polynomial.C (wB k))

/-! ### The glued schemes -/

/-- **The pinching `X₀` of `E × 𝔸¹` along `E × {0}` and `y`.** -/
noncomputable def X0 : Scheme.{u} := TwoChartGlue.glued (f0 k) (f1 k)

/-- **`E × 𝔸¹`**, glued from `U_A × 𝔸¹` and `U_B × 𝔸¹`. -/
noncomputable def EA1 : Scheme.{u} := TwoChartGlue.glued (p0 k) (p1 k)

/-- `ν₀ : E × 𝔸¹ → X₀`, chartwise `Spec A[z] → Spec R0`, `Spec B[z] → Spec R1`. -/
noncomputable def nu0 : EA1 k ⟶ X0 k :=
  TwoChartGlue.desc (p0 k) (p1 k)
    (Spec.map (CommRingCat.ofHom (pr₂ (piA k) (beta0 k))) ≫ TwoChartGlue.ι₀ (f0 k) (f1 k))
    (Spec.map (CommRingCat.ofHom (pr₂ (piB k) (beta1 k))) ≫ TwoChartGlue.ι₁ (f0 k) (f1 k)) (by
      have e0 : (pr₂ (pi01 k) (beta01 k)).comp (f0 k) = (p0 k).comp (pr₂ (piA k) (beta0 k)) :=
        rfl
      have e1 : (pr₂ (pi01 k) (beta01 k)).comp (f1 k) = (p1 k).comp (pr₂ (piB k) (beta1 k)) :=
        rfl
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← e0,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, TwoChartGlue.compat,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1])

@[simp] theorem ι₀_nu0 : TwoChartGlue.ι₀ (p0 k) (p1 k) ≫ nu0 k =
    Spec.map (CommRingCat.ofHom (pr₂ (piA k) (beta0 k))) ≫ TwoChartGlue.ι₀ (f0 k) (f1 k) :=
  TwoChartGlue.ι₀_desc _ _ _ _ _

@[simp] theorem ι₁_nu0 : TwoChartGlue.ι₁ (p0 k) (p1 k) ≫ nu0 k =
    Spec.map (CommRingCat.ofHom (pr₂ (piB k) (beta1 k))) ≫ TwoChartGlue.ι₁ (f0 k) (f1 k) :=
  TwoChartGlue.ι₁_desc _ _ _ _ _

#print axioms isLocalization_f0
#print axioms isLocalization_f1
#print axioms X0
#print axioms nu0

end Pcf.Examples.PaperP.MonodromyLossPinchGlue
