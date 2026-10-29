/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossCurveScheme
public import Pcf.Examples.PaperP.BasilicaProjectiveScheme

/-!
# The coordinate `y : E → ℙ¹` of `ex:monodromy-loss` as a scheme morphism

For `paper-p.tex`, Example `ex:monodromy-loss`: the variety `X` pinches `E × {0}` along
`y : E → ℙ¹`. Here `y` is built as an actual morphism from the glued curve `E` to the
projective line `Proj k[u, v]` of `BasilicaProjectiveScheme` (the same model as the return map
`g` of `MonodromyLossReturnScheme`), with `y = u / v`.

* `awayEval`: the ring map `k[u,v]_{(f)} → T`, `P / fⁿ ↦ P(x) / f(x)ⁿ`, for a point `x ∈ T²`
  with `f(x)` a unit. `awayEval_comp`, `awayEval_awayMap`, `awayEval_smul` are its functoriality,
  compatibility with `awayMap` and invariance under rescaling `x ↦ c x`.
* `yChartA : Spec A → ℙ¹` is `(x, y) ↦ [y : 1]` on `D₊(v)`; `yChartB : Spec B → ℙ¹` is
  `(s, w) ↦ [1 : w]` on `D₊(u)`.
* **`yMap : E ⟶ ℙ¹`**, with `ιA_yMap`, `ιB_yMap`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossCurve

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open BasilicaProjectiveScheme (Index Coordinates grading)

section AwayEval

variable (k : Type u) [Field k]

/-- Homogeneous polynomials scale: `P(c x) = cᵐ P(x)`. -/
theorem aeval_smul_of_isHomogeneous {T : Type*} [CommRing T] [Algebra k T] {σ : Type*}
    {P : MvPolynomial σ k} {m : ℕ} (hP : P.IsHomogeneous m) (c : T) (x : σ → T) :
    aeval (fun i => c * x i) P = c ^ m * aeval x P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.mul_sum, aeval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hP.degree_eq_sum_deg_support hd
  rw [Finsupp.prod_congr (g2 := fun i e => c ^ e * x i ^ e) (fun i _ => mul_pow c (x i) _),
    Finsupp.prod_mul]
  have hc : (d.prod fun _ e => c ^ e) = c ^ m := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
  rw [hc]
  ring

variable {k} {T : Type u} [CommRing T] [Algebra k T]

/-- The evaluation `k[u,v]_{(f)} → T`, `P / fⁿ ↦ P(x) / f(x)ⁿ`, at a point `x` with `f(x)` a
unit. -/
noncomputable def awayEval (f : Coordinates k) (x : Index → T) (h : IsUnit (aeval x f)) :
    Away (grading k) f →+* T :=
  (IsLocalization.Away.lift f (S := Localization.Away f) (g := (aeval x).toRingHom) h).comp
    (algebraMap (Away (grading k) f) (Localization.Away f))

theorem awayEval_comp {T' : Type u} [CommRing T'] [Algebra k T'] (φ : T →ₐ[k] T')
    (f : Coordinates k) (x : Index → T) (h : IsUnit (aeval x f))
    (h' : IsUnit (aeval (fun i => φ (x i)) f)) :
    (φ : T →+* T').comp (awayEval f x h) = awayEval f (fun i => φ (x i)) h' := by
  have key : (φ : T →+* T').comp
      (IsLocalization.Away.lift f (S := Localization.Away f) (g := (aeval x).toRingHom) h) =
      IsLocalization.Away.lift f (S := Localization.Away f)
        (g := (aeval fun i => φ (x i)).toRingHom) h' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    exact MvPolynomial.comp_aeval_apply (f := x) φ a
  ext z
  exact DFunLike.congr_fun key _

theorem awayEval_awayMap {f g x : Coordinates k} {e : ℕ} (hg : g ∈ grading k e)
    (hx : x = f * g) (y : Index → T) (h : IsUnit (aeval y x)) (h' : IsUnit (aeval y f)) :
    (awayEval x y h).comp (awayMap (grading k) hg hx) = awayEval f y h' := by
  ext z
  simp only [awayEval, RingHom.comp_apply]
  change IsLocalization.Away.lift x h (awayMap (grading k) hg hx z).val = _
  rw [val_awayMap]
  change _ = IsLocalization.Away.lift f h' z.val
  generalize z.val = w
  have key : (IsLocalization.Away.lift x h).comp (Localization.awayLift
      (algebraMap (Coordinates k) (Localization.Away x)) f
      (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x))) =
      IsLocalization.Away.lift f (S := Localization.Away f) h' :=
    IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => by
      simp [Localization.awayLift, IsLocalization.Away.lift_eq])
  exact DFunLike.congr_fun key w

/-- `awayEval` is invariant under rescaling the point: `[c x] = [x]`. -/
theorem awayEval_smul {f : Coordinates k} {d : ℕ} (hf : f ∈ grading k d) (c : T)
    (x : Index → T) (h₁ : IsUnit (aeval (fun i => c * x i) f)) (h₂ : IsUnit (aeval x f)) :
    awayEval f (fun i => c * x i) h₁ = awayEval f x h₂ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading k) hf z
  simp only [awayEval, RingHom.comp_apply]
  let s : Submonoid.powers f := ⟨f ^ n, by use n⟩
  change IsLocalization.Away.lift f h₁ (Localization.mk a s) =
    IsLocalization.Away.lift f h₂ (Localization.mk a s)
  rw [Localization.mk_eq_mk', IsLocalization.Away.lift, IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  have hs := (IsLocalization.lift_mk'_spec (M := Submonoid.powers f) (S := Localization.Away f)
    (g := (aeval x).toRingHom) (hg := by
      rintro ⟨_, m, rfl⟩; simpa using h₂.pow m) a _ s).mp rfl
  have ha' : a.IsHomogeneous (n • d) := (mem_homogeneousSubmodule _ _).mp ha
  have hf' : f.IsHomogeneous d := (mem_homogeneousSubmodule _ _).mp hf
  have hsf : (s : Coordinates k) = f ^ n := rfl
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hsf, map_pow] at hs ⊢
  rw [aeval_smul_of_isHomogeneous k ha', aeval_smul_of_isHomogeneous k hf', hs]
  ring

end AwayEval

section YMap

variable (k : Type u) [Field k]

local notation "uu" => (X (Sum.inl 0) : Coordinates k)
local notation "vv" => (X (Sum.inr ()) : Coordinates k)
local notation "P1" => Proj (grading k)

/-- `(x, y) ↦ [y : 1]` on the chart `Spec A`. -/
noncomputable def valsA : Index → A k := Sum.elim (fun _ => yA k) (fun _ => 1)

/-- `(s, w) ↦ [1 : w]` on the chart `Spec B` (`w = 1/y`). -/
noncomputable def valsB : Index → B k := Sum.elim (fun _ => 1) (fun _ => wB k)

/-- `[y : 1]` on the overlap `Spec A[1/y]`. -/
noncomputable def valsAy : Index → Ay k := Sum.elim (fun _ => algebraMap (A k) (Ay k) (yA k))
  (fun _ => 1)

theorem valsA_v : IsUnit (aeval (valsA k) vv) := by simp [valsA]
theorem valsB_u : IsUnit (aeval (valsB k) uu) := by simp [valsB]
theorem valsAy_v : IsUnit (aeval (valsAy k) vv) := by simp [valsAy]
theorem valsAy_u : IsUnit (aeval (valsAy k) uu) := by
  simp only [valsAy, aeval_X, Sum.elim_inl]
  exact IsUnit.of_mul_eq_one _ (y_mul_invY k)
theorem valsAy_uv : IsUnit (aeval (valsAy k) (uu * vv)) := by
  rw [map_mul]; exact (valsAy_u k).mul (valsAy_v k)

/-- `y` on the finite chart: `Spec A → D₊(v) ⊆ ℙ¹`, `(x, y) ↦ [y : 1]`. -/
noncomputable def yChartA : Spec (.of (A k)) ⟶ P1 :=
  Spec.map (CommRingCat.ofHom (awayEval vv (valsA k) (valsA_v k))) ≫
    Proj.awayι (grading k) vv (isHomogeneous_X k _) Nat.zero_lt_one

/-- `y` on the chart at infinity: `Spec B → D₊(u) ⊆ ℙ¹`, `(s, w) ↦ [1 : w]`. -/
noncomputable def yChartB : Spec (.of (B k)) ⟶ P1 :=
  Spec.map (CommRingCat.ofHom (awayEval uu (valsB k) (valsB_u k))) ≫
    Proj.awayι (grading k) uu (isHomogeneous_X k _) Nat.zero_lt_one

/-- Both chart maps restrict on `Spec A[1/y]` to `[y : 1]` on `D₊(uv)`. -/
theorem jA_yChartA : jA k ≫ yChartA k =
    Spec.map (CommRingCat.ofHom (awayEval (uu * vv) (valsAy k) (valsAy_uv k))) ≫
      Proj.awayι (grading k) (uu * vv) ((isHomogeneous_X k _).mul (isHomogeneous_X k _))
        (by norm_num) := by
  have e1 : (algebraMap (A k) (Ay k)).comp (awayEval vv (valsA k) (valsA_v k)) =
      awayEval vv (valsAy k) (valsAy_v k) := by
    have := awayEval_comp (IsScalarTower.toAlgHom k (A k) (Ay k)) vv (valsA k) (valsA_v k)
      (by convert valsAy_v k using 3; funext i; rcases i with _ | _ <;> simp [valsA, valsAy])
    refine this.trans ?_
    congr 1
    funext i; rcases i with _ | _ <;> simp [valsA, valsAy]
  have e2 := awayEval_awayMap (isHomogeneous_X k (Sum.inl 0)) (mul_comm uu vv) (valsAy k)
    (valsAy_uv k) (valsAy_v k)
  rw [jA, yChartA, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, ← e2,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]

theorem jB_yChartB : jB k ≫ yChartB k =
    Spec.map (CommRingCat.ofHom (awayEval (uu * vv) (valsAy k) (valsAy_uv k))) ≫
      Proj.awayι (grading k) (uu * vv) ((isHomogeneous_X k _).mul (isHomogeneous_X k _))
        (by norm_num) := by
  have hB : IsUnit (aeval (fun i => BtoAyₐ k (valsB k i)) uu) := by simp [valsB]
  have e1 : (BtoAy k).comp (awayEval uu (valsB k) (valsB_u k)) =
      awayEval uu (valsAy k) (valsAy_u k) := by
    have := awayEval_comp (BtoAyₐ k) uu (valsB k) (valsB_u k) hB
    refine this.trans ?_
    rw [← awayEval_smul (isHomogeneous_X k (Sum.inl 0)) (algebraMap (A k) (Ay k) (yA k))
      _ (by convert valsAy_u k using 3; funext i; rcases i with _ | _ <;>
        simp [valsB, valsAy, BtoAyₐ, BtoAy, liftB_w]) hB]
    congr 1
    funext i; rcases i with _ | _ <;> simp [valsB, valsAy, BtoAyₐ, BtoAy, liftB_w]
  have e2 := awayEval_awayMap (isHomogeneous_X k (Sum.inr ())) (rfl : uu * vv = uu * vv)
    (valsAy k) (valsAy_uv k) (valsAy_u k)
  rw [jB, yChartB, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, ← e2,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]

/-- **The coordinate `y : E → ℙ¹`** of `ex:monodromy-loss`, as a morphism of schemes. -/
noncomputable def yMap : E k ⟶ P1 :=
  desc k (yChartA k) (yChartB k) ((jA_yChartA k).trans (jB_yChartB k).symm)

@[simp] theorem ιA_yMap : ιA k ≫ yMap k = yChartA k := ιA_desc k _ _ _
@[simp] theorem ιB_yMap : ιB k ≫ yMap k = yChartB k := ιB_desc k _ _ _

end YMap

#print axioms awayEval_smul
#print axioms yMap

end Pcf.Examples.PaperP.MonodromyLossCurve
