/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CharPExceptionalChart
public import Pcf.Bounding.AllCodimBlowupExceptionalChart
public import Pcf.Bounding.AllCodimBlowupProjChart

/-!
# The actual `y`-chart of `Bl_A(X)` in `ex:charp-exceptional-fibre-paper`

`paper-p.tex`, Example `ex:charp-exceptional-fibre-paper`, takes
`X = Spec k[x,y,z,t]/(x^p - t y^p - z^(p+1))`, `A = V(x,y,z)`, and asserts that on
the `y`-chart of `Bl_A(X)`, with `x = yu` and `z = yv`, the coordinate ring is
`k[y,u,v]` and the exceptional divisor `D = V(y)` maps to `A = Spec k[t]` by
`t = u^p`.

Here the blow-up is the repository's actual Rees blow-up
`Pcf.Bounding.AllCodimBlowup.reesProj I` (Mathlib `Proj` of the Rees algebra), whose
standard chart at `y` is an open immersion from the spectrum of the affine blow-up
algebra `R[I/y] ⊂ R_y` (`reesProjChartEquiv`). We identify `R[I/y]` with the polynomial
ring `k[y,u,v]`, so the `y`-chart of the actual blow-up is `Spec k[y,u,v]`; we identify the
pulled-back centre with `(y)`; and on it `t ≡ u^p`.

The identification holds over any field and any `p`; the characteristic enters only
through the fibre statement in `CharPExceptionalFibre`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CharPExceptionalBlowup

open MvPolynomial CategoryTheory
open Pcf.Bounding.AllCodimBlowup
open Pcf.Examples.PaperP.CharPExceptionalChart (ChartBase)

set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

abbrev Ambient := MvPolynomial (Fin 4) k

/-- The equation `x^p - t y^p - z^(p+1)`, with variables `x,y,z,t = X 0, X 1, X 2, X 3`. -/
noncomputable def hyperEquation : Ambient k :=
  X 0 ^ p - X 3 * X 1 ^ p - X 2 ^ (p + 1)

/-- The coordinate ring of the manuscript's hypersurface `X`. -/
abbrev HyperRing := Ambient k ⧸ Ideal.span {hyperEquation k p}

noncomputable def hx : HyperRing k p := Ideal.Quotient.mk _ (X 0)
noncomputable def hy : HyperRing k p := Ideal.Quotient.mk _ (X 1)
noncomputable def hz : HyperRing k p := Ideal.Quotient.mk _ (X 2)
noncomputable def ht : HyperRing k p := Ideal.Quotient.mk _ (X 3)

theorem hyper_relation : hx k p ^ p - ht k p * hy k p ^ p - hz k p ^ (p + 1) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span {hyperEquation k p}) (hyperEquation k p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  simp only [hyperEquation] at h
  exact h

/-- The centre `A = V(x,y,z)`. -/
noncomputable def center : Ideal (HyperRing k p) := Ideal.span {hx k p, hy k p, hz k p}

noncomputable abbrev centerY : center k p := ⟨hy k p, Ideal.subset_span (by simp)⟩
noncomputable abbrev centerX : center k p := ⟨hx k p, Ideal.subset_span (by simp)⟩
noncomputable abbrev centerZ : center k p := ⟨hz k p, Ideal.subset_span (by simp)⟩

/-- The affine blow-up algebra `R[I/y]` of the actual Rees chart. -/
noncomputable abbrev YChart := affineBlowupChart (center k p) (centerY k p)

abbrev Ry := Localization.Away (hy k p)

noncomputable def yInv : Ry k p := IsLocalization.Away.invSelf (hy k p)

/-- The chart coordinates: `y ↦ y`, `u ↦ x/y`, `v ↦ z/y`. -/
noncomputable def chartCoords : ChartBase k →ₐ[k] Ry k p :=
  aeval ![algebraMap _ _ (hy k p), algebraMap _ _ (hx k p) * yInv k p,
    algebraMap _ _ (hz k p) * yInv k p]

theorem y_mul_yInv : algebraMap (HyperRing k p) (Ry k p) (hy k p) * yInv k p = 1 :=
  IsLocalization.Away.mul_invSelf _

@[simp] theorem chartCoords_X0 : chartCoords k p (X 0) = algebraMap _ _ (hy k p) := by
  simp [chartCoords]
@[simp] theorem chartCoords_X1 :
    chartCoords k p (X 1) = algebraMap _ _ (hx k p) * yInv k p := by
  simp [chartCoords]
@[simp] theorem chartCoords_X2 :
    chartCoords k p (X 2) = algebraMap _ _ (hz k p) * yInv k p := by
  simp [chartCoords]

/-- In `R_y`, `t = (x/y)^p - y (z/y)^(p+1)`. -/
theorem t_eq_chart :
    algebraMap (HyperRing k p) (Ry k p) (ht k p) =
      (algebraMap _ _ (hx k p) * yInv k p) ^ p -
        algebraMap _ _ (hy k p) * (algebraMap _ _ (hz k p) * yInv k p) ^ (p + 1) := by
  have hrel := congrArg (algebraMap (HyperRing k p) (Ry k p)) (hyper_relation k p)
  have hu := y_mul_yInv k p
  simp only [map_sub, map_mul, map_pow, map_zero] at hrel
  set Y := algebraMap (HyperRing k p) (Ry k p) (hy k p)
  set Xx := algebraMap (HyperRing k p) (Ry k p) (hx k p)
  set Z := algebraMap (HyperRing k p) (Ry k p) (hz k p)
  set T := algebraMap (HyperRing k p) (Ry k p) (ht k p)
  set w := yInv k p
  have hT : T = T * (Y * w) ^ p := by rw [hu, one_pow, mul_one]
  rw [hT]
  have : T * (Y * w) ^ p = (Xx ^ p - Z ^ (p + 1)) * w ^ p := by
    rw [mul_pow, ← mul_assoc, show Xx ^ p - Z ^ (p + 1) = T * Y ^ p by linear_combination hrel]
  rw [this]
  have hw : Y * w ^ (p + 1) = w ^ p := by
    rw [pow_succ, ← mul_assoc, mul_comm Y, mul_assoc, hu, mul_one]
  linear_combination (Z ^ (p + 1)) * hw

/-- Every function on `X` lies in the image of the chart coordinates. -/
theorem algebraMap_mem_range (r : HyperRing k p) :
    algebraMap (HyperRing k p) (Ry k p) r ∈ (chartCoords k p).range := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction q using MvPolynomial.induction_on with
  | C c =>
      refine ⟨C c, ?_⟩
      change chartCoords k p (C c) = _
      rw [chartCoords, MvPolynomial.aeval_C]
      rfl
  | add a b ha hb => simpa only [map_add] using add_mem ha hb
  | mul_X a i ha =>
      rw [map_mul, map_mul]
      refine mul_mem ha ?_
      fin_cases i
      · refine ⟨X 0 * X 1, ?_⟩
        change chartCoords k p _ = _
        rw [map_mul, chartCoords_X0, chartCoords_X1, mul_left_comm, y_mul_yInv, mul_one]
        rfl
      · exact ⟨X 0, chartCoords_X0 k p⟩
      · refine ⟨X 0 * X 2, ?_⟩
        change chartCoords k p _ = _
        rw [map_mul, chartCoords_X0, chartCoords_X2, mul_left_comm, y_mul_yInv, mul_one]
        rfl
      · refine ⟨X 1 ^ p - X 0 * X 2 ^ (p + 1), ?_⟩
        change chartCoords k p _ = _
        rw [map_sub, map_mul, map_pow, map_pow, chartCoords_X0, chartCoords_X1, chartCoords_X2]
        exact (t_eq_chart k p).symm

/-- The image of the chart coordinates is exactly the actual affine blow-up
algebra `R[I/y]`. -/
theorem mem_range_chartCoords_iff (w : Ry k p) :
    w ∈ (chartCoords k p).range ↔ w ∈ YChart k p := by
  constructor
  · rintro ⟨q, rfl⟩
    induction q using MvPolynomial.induction_on with
    | C c =>
        change chartCoords k p (C c) ∈ YChart k p
        rw [chartCoords, MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply k (HyperRing k p)]
        exact (YChart k p).algebraMap_mem (algebraMap k (HyperRing k p) c)
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
    | mul_X a i ha =>
        rw [map_mul]
        refine mul_mem ha ?_
        fin_cases i
        · simp
        · change chartCoords k p (X 1) ∈ YChart k p
          rw [chartCoords_X1]
          exact ratio_mem_affineBlowupChart (center k p) (centerY k p) (centerX k p)
        · change chartCoords k p (X 2) ∈ YChart k p
          rw [chartCoords_X2]
          exact ratio_mem_affineBlowupChart (center k p) (centerY k p) (centerZ k p)
  · intro hw
    change w ∈ affineBlowupChart (center k p) (centerY k p) at hw
    rw [affineBlowupChart_eq_adjoin_ratios] at hw
    induction hw using Algebra.adjoin_induction with
    | mem z hz =>
        obtain ⟨⟨b, hb⟩, rfl⟩ := hz
        change algebraMap _ _ b * yInv k p ∈ (chartCoords k p).range
        induction hb using Submodule.span_induction with
        | mem g hg =>
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            rcases hg with rfl | rfl | rfl
            · exact ⟨X 1, chartCoords_X1 k p⟩
            · exact ⟨1, by rw [map_one, y_mul_yInv]⟩
            · exact ⟨X 2, chartCoords_X2 k p⟩
        | zero => simp
        | add a b _ _ ha hb => simpa only [map_add, add_mul] using add_mem ha hb
        | smul r a _ ha =>
            rw [smul_eq_mul, map_mul, mul_assoc]
            exact mul_mem (algebraMap_mem_range k p r) ha
    | algebraMap r => exact algebraMap_mem_range k p r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

/-- Back map `R → k[y,u,v][1/y]`: `x ↦ yu`, `y ↦ y`, `z ↦ yv`,
`t ↦ u^p - y v^(p+1)`. -/
noncomputable def backAmbient : Ambient k →ₐ[k] ChartBase k :=
  aeval ![X 0 * X 1, X 0, X 0 * X 2, X 1 ^ p - X 0 * X 2 ^ (p + 1)]

noncomputable def back : HyperRing k p →ₐ[k] ChartBase k :=
  Ideal.Quotient.liftₐ _ (backAmbient k p) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : backAmbient k p (hyperEquation k p) = 0 := by
      simp only [hyperEquation, backAmbient, map_sub, map_mul, map_pow, aeval_X]
      simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [mul_pow, pow_succ]
      ring
    rw [this, mul_zero])

@[simp] theorem back_hy : back k p (hy k p) = X 0 := by
  change backAmbient k p (X 1) = _
  simp [backAmbient]
@[simp] theorem back_hx : back k p (hx k p) = X 0 * X 1 := by
  change backAmbient k p (X 0) = _
  simp [backAmbient]
@[simp] theorem back_hz : back k p (hz k p) = X 0 * X 2 := by
  change backAmbient k p (X 2) = _
  simp [backAmbient]

abbrev ChartAway := Localization.Away (X 0 : ChartBase k)

noncomputable def backAway : Ry k p →+* ChartAway k :=
  IsLocalization.Away.lift (hy k p)
    (g := (algebraMap (ChartBase k) (ChartAway k)).comp (back k p).toRingHom) (by
      change IsUnit (algebraMap (ChartBase k) (ChartAway k) (back k p (hy k p)))
      rw [back_hy]
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem backAway_algebraMap (r : HyperRing k p) :
    backAway k p (algebraMap _ _ r) = algebraMap (ChartBase k) (ChartAway k) (back k p r) :=
  IsLocalization.lift_eq _ _

theorem backAway_yInv :
    algebraMap (ChartBase k) (ChartAway k) (X 0) * backAway k p (yInv k p) = 1 := by
  have h := congrArg (backAway k p) (y_mul_yInv k p)
  rw [map_mul, map_one, backAway_algebraMap, back_hy] at h
  exact h

theorem backAway_comp_chartCoords :
    (backAway k p).comp (chartCoords k p).toRingHom =
      algebraMap (ChartBase k) (ChartAway k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change backAway k p (chartCoords k p (C c)) = _
    rw [chartCoords, aeval_C, IsScalarTower.algebraMap_apply k (HyperRing k p) (Ry k p),
      backAway_algebraMap, AlgHom.commutes]
    rfl
  · intro i
    change backAway k p (chartCoords k p (X i)) = _
    have hu := backAway_yInv k p
    fin_cases i
    · simp only [Fin.zero_eta, chartCoords_X0, backAway_algebraMap, back_hy]
    · simp only [Fin.mk_one, chartCoords_X1, map_mul, backAway_algebraMap, back_hx]
      linear_combination (algebraMap (ChartBase k) (ChartAway k) (X 1)) * hu
    · simp only [Fin.reduceFinMk, chartCoords_X2, map_mul, backAway_algebraMap, back_hz]
      linear_combination (algebraMap (ChartBase k) (ChartAway k) (X 2)) * hu

/-- The chart coordinates are injective. -/
theorem chartCoords_injective : Function.Injective (chartCoords k p) := by
  have hinj : Function.Injective (algebraMap (ChartBase k) (ChartAway k)) :=
    IsLocalization.injective (ChartAway k)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  intro a b hab
  apply hinj
  rw [← backAway_comp_chartCoords k p]
  exact congrArg (backAway k p) hab

/-- **The `y`-chart of the actual blow-up has coordinate ring `k[y,u,v]`.** The affine
blow-up algebra `R[I/y]` is isomorphic to the polynomial ring, with `y ↦ y`,
`u ↦ x/y`, `v ↦ z/y`.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
noncomputable def chartEquiv : ChartBase k ≃+* YChart k p :=
  RingEquiv.ofBijective
    ((chartCoords k p).toRingHom.codRestrict (YChart k p).toSubsemiring
      (fun q => (mem_range_chartCoords_iff k p _).mp ⟨q, rfl⟩))
    ⟨fun a b h => chartCoords_injective k p (congrArg Subtype.val h), by
      rintro ⟨w, hw⟩
      obtain ⟨q, hq⟩ := (mem_range_chartCoords_iff k p w).mpr hw
      exact ⟨q, Subtype.ext hq⟩⟩

@[simp] theorem chartEquiv_val (q : ChartBase k) :
    (chartEquiv k p q : Ry k p) = chartCoords k p q := rfl

theorem chartEquiv_X0 :
    chartEquiv k p (X 0) = algebraMap (HyperRing k p) (YChart k p) (hy k p) :=
  Subtype.ext (chartCoords_X0 k p)

/-- In the chart, `x = y u` (with `u = X 1`). -/
theorem chart_x_eq :
    algebraMap (HyperRing k p) (YChart k p) (hx k p) = chartEquiv k p (X 0 * X 1) := by
  apply Subtype.ext
  change _ = chartCoords k p (X 0 * X 1)
  rw [map_mul, chartCoords_X0, chartCoords_X1, mul_left_comm, y_mul_yInv, mul_one]
  rfl

/-- In the chart, `z = y v` (with `v = X 2`). -/
theorem chart_z_eq :
    algebraMap (HyperRing k p) (YChart k p) (hz k p) = chartEquiv k p (X 0 * X 2) := by
  apply Subtype.ext
  change _ = chartCoords k p (X 0 * X 2)
  rw [map_mul, chartCoords_X0, chartCoords_X2, mul_left_comm, y_mul_yInv, mul_one]
  rfl

/-- In the chart, `t = u^p - y v^(p+1)`: the strict-transform equation. -/
theorem chart_t_eq :
    algebraMap (HyperRing k p) (YChart k p) (ht k p) =
      chartEquiv k p (X 1 ^ p - X 0 * X 2 ^ (p + 1)) := by
  apply Subtype.ext
  change _ = chartCoords k p (X 1 ^ p - X 0 * X 2 ^ (p + 1))
  rw [map_sub, map_mul, map_pow, map_pow, chartCoords_X0, chartCoords_X1, chartCoords_X2]
  exact t_eq_chart k p

/-- The strict-transform chart ring `k[y,u,v,t]/(u^p - t - y v^(p+1))` of
`CharPExceptionalChart` is isomorphic to the actual affine blow-up algebra. -/
noncomputable def strictTransformEquiv : CharPExceptionalChart.ChartRing k p ≃+* YChart k p :=
  (CharPExceptionalChart.chartRingEquiv k p).trans (chartEquiv k p)

/-- The exceptional ideal `I·R[I/y]` on the chart is `(y)`.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem exceptionalIdeal_eq :
    (center k p).map (algebraMap (HyperRing k p) (YChart k p)) =
      Ideal.span {chartEquiv k p (X 0)} := by
  rw [centerIdeal_map_affineBlowupChart_eq_span, chartEquiv_X0]

/-- The exceptional ideal corresponds to `(y) ⊂ k[y,u,v]`. -/
theorem exceptionalIdeal_comap :
    ((center k p).map (algebraMap (HyperRing k p) (YChart k p))).comap
        (chartEquiv k p).toRingHom = Ideal.span {(X 0 : ChartBase k)} := by
  rw [exceptionalIdeal_eq]
  ext q
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact map_dvd_iff (chartEquiv k p)

/-- On the exceptional divisor of the actual chart, `t ≡ u^p` modulo `(y)`. -/
theorem exceptional_t_sub_u_pow_mem :
    algebraMap (HyperRing k p) (YChart k p) (ht k p) - chartEquiv k p (X 1) ^ p ∈
      (center k p).map (algebraMap (HyperRing k p) (YChart k p)) := by
  rw [exceptionalIdeal_eq, chart_t_eq, ← map_pow, ← map_sub,
    show (X 1 ^ p - X 0 * X 2 ^ (p + 1) - X 1 ^ p : ChartBase k) =
      X 0 * (-(X 2 ^ (p + 1))) by ring, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- The degree-zero `Proj` chart of the Rees algebra at `y t` is `k[y,u,v]`. -/
noncomputable def reesChartEquiv :
    reesProjChart (center k p) (centerY k p) ≃+* ChartBase k :=
  (reesProjChartEquiv (center k p) (centerY k p)).trans (chartEquiv k p).symm

/-- `Spec k[y,u,v]` is isomorphic to the standard `Proj` chart at `y t`. -/
noncomputable def yChartIso :
    AlgebraicGeometry.Spec (.of (ChartBase k)) ≅
      AlgebraicGeometry.Spec (.of (reesProjChart (center k p) (centerY k p))) :=
  AlgebraicGeometry.Scheme.Spec.mapIso (reesChartEquiv k p).toCommRingCatIso.op

/-- The `y`-chart of the actual Rees blow-up `Bl_A(X)`, as an open immersion of
`Spec k[y,u,v]`.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
noncomputable def yChartOpen :
    AlgebraicGeometry.Spec (.of (ChartBase k)) ⟶ reesProj (center k p) :=
  (yChartIso k p).hom ≫ reesProjChartOpen (center k p) (centerY k p)

/-- `paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
instance yChartOpen_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (yChartOpen k p) := by
  unfold yChartOpen
  infer_instance

#print axioms hyper_relation
#print axioms t_eq_chart
#print axioms mem_range_chartCoords_iff
#print axioms chartCoords_injective
#print axioms chartEquiv
#print axioms chart_x_eq
#print axioms chart_z_eq
#print axioms chart_t_eq
#print axioms strictTransformEquiv
#print axioms exceptionalIdeal_eq
#print axioms exceptionalIdeal_comap
#print axioms exceptional_t_sub_u_pow_mem
#print axioms yChartOpen_isOpenImmersion

end Pcf.Examples.PaperP.CharPExceptionalBlowup
