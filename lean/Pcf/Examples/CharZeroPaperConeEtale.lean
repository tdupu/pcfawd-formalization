/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperConeBranch
public import Pcf.Examples.CharZeroPaperConeCharts
public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI
public import Pcf.Bounding.SchemeBridge
public import Pcf.Bounding.FiniteTypeRegularLocus
public import Pcf.PaperCharZero.SupportingDictionary
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Étale charts, normality, singular locus and empty branch in `ex:branch-singular`

This file completes `ex:branch-singular` of `paper.tex` on the actual schemes of
`CharZeroPaperConeBranch`.

* **Explicit charts.** Over `D(x)` the localized source ring `k[u,v]_{u²}` is
  `k[Y]_x[T]/(T²-x)` with `T ↦ u`; the inverse sends `u ↦ T` and recovers
  `v = yT/x = y/T` (`chartEquivX`). Symmetrically over `D(z)` with `T ↦ v`
  (`chartEquivZ`). Since `x` (resp. `z`) and `2` are units, `T²-x` is a standard
  étale relation, and the restrictions of the actual morphism `coneMap` over the
  two opens are étale (`coneMap_restrict_basicOpen_x_etale`, `..._z_etale`).
* **Normality and singular locus.** The cone is normal (`cone_isNormal`), the
  vertex has height two (`vertex_height`), the local ring at the vertex is not
  regular (its maximal ideal needs three generators, `three_le_spanFinrank_vertex`),
  and every other local ring is regular, being a localization of `k[a,b]_a`
  (`targetXEquiv`, `targetZEquiv`). Hence `stalkSingularLocus (cone K) = {vertex K}`.
* **Empty branch.** Every source divisor maps off the vertex, so its stalk map is
  formally étale by the charts; the étale/index-one dictionary
  (`ramificationIdx_eq_one_iff_formallyEtale_charZero`) gives ramification index one,
  and the actual normalized branch support of `coneMap` is empty
  (`normalized_cone_branch_empty`).

`ex_branch_singular` assembles the whole example. The coordinates, the invariant ring,
the vertex locus, the lines and the chart localizations are in `CharZeroPaperConeCharts`.
-/

@[expose] public section
noncomputable section
namespace Pcf.Examples.CharZeroPaperConeBranch
open CategoryTheory AlgebraicGeometry Polynomial Pcf.PaperCharZero
universe u
variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency false

/-! ### The chart over `D(x)` -/

/-- The cone coordinate `x` in the target localization `k[Y]_x`. -/
abbrev xX : TargetX K := algebraMap (ConeRing K) (TargetX K) (coneX K)
/-- The cone coordinate `y` in the target localization `k[Y]_x`. -/
abbrev yX : TargetX K := algebraMap (ConeRing K) (TargetX K) (coneY K)
/-- The cone coordinate `z` in the target localization `k[Y]_x`. -/
abbrev zX : TargetX K := algebraMap (ConeRing K) (TargetX K) (coneZ K)
/-- The inverse of `x` in `k[Y]_x`. -/
abbrev invX : TargetX K := IsLocalization.Away.invSelf (coneX K)

theorem xX_mul_invX : xX K * invX K = 1 := IsLocalization.Away.mul_invSelf _

theorem yX_sq : yX K ^ 2 = xX K * zX K := by
  simp only [← map_pow, ← map_mul, coneY_sq]

/-- The monic relation `T² - x` over `k[Y]_x`. -/
def chartRelX : (TargetX K)[X] := X ^ 2 - C (xX K)

/-- The source coordinate `u` in the source localization `k[u,v]_{u²}`. -/
abbrev uX : SourceX K := algebraMap (SourceRing K) (SourceX K) (MvPolynomial.X 0)
/-- The source coordinate `v` in the source localization `k[u,v]_{u²}`. -/
abbrev vX : SourceX K := algebraMap (SourceRing K) (SourceX K) (MvPolynomial.X 1)

theorem chartX_xX : chartX K (xX K) = uX K ^ 2 :=
  (chartX_on_cone_coordinate K _).trans
    ((congrArg (algebraMap (SourceRing K) (SourceX K)) (coneParam_x K)).trans (map_pow _ _ _))

theorem chartX_yX : chartX K (yX K) = uX K * vX K := by
  rw [chartX_on_cone_coordinate, coneParam_y, map_mul]

/-- The root `T ↦ u`. -/
def adjoinToSourceX : AdjoinRoot (chartRelX K) →+* SourceX K :=
  AdjoinRoot.lift (chartX K).toRingHom (uX K) (by
    simp only [chartRelX, eval₂_sub, eval₂_X_pow, eval₂_C]
    change uX K ^ 2 - chartX K (xX K) = 0
    rw [chartX_xX, sub_self])

@[simp] theorem adjoinToSourceX_root : adjoinToSourceX K (AdjoinRoot.root _) = uX K :=
  AdjoinRoot.lift_root _

@[simp] theorem adjoinToSourceX_of (t : TargetX K) :
    adjoinToSourceX K (AdjoinRoot.of _ t) = chartX K t :=
  AdjoinRoot.lift_of _

/-- The root `T` of `T² - x`. -/
abbrev rootX : AdjoinRoot (chartRelX K) := AdjoinRoot.root (chartRelX K)
/-- Scalars from `k[Y]_x`. -/
abbrev ofX (t : TargetX K) : AdjoinRoot (chartRelX K) := AdjoinRoot.of (chartRelX K) t

theorem rootX_sq : rootX K ^ 2 = ofX K (xX K) := by
  have h : AdjoinRoot.mk (chartRelX K) (X ^ 2 - C (xX K)) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  exact h

/-- On the plane, `u ↦ T` and `v ↦ yT/x`. -/
def planeToAdjoinX : SourceRing K →+* AdjoinRoot (chartRelX K) :=
  MvPolynomial.eval₂Hom ((AdjoinRoot.of (chartRelX K)).comp (algebraMap K (TargetX K)))
    ![rootX K, ofX K (yX K * invX K) * rootX K]

theorem planeToAdjoinX_cone (r : ConeRing K) :
    planeToAdjoinX K (Cusp.coneParam K r) = ofX K (algebraMap (ConeRing K) (TargetX K) r) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  change planeToAdjoinX K (MvPolynomial.aeval (Cusp.coneMap K) p) = _
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [planeToAdjoinX]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X]
    congr 1
    have hx := xX_mul_invX K
    have hy := yX_sq K
    have hr := rootX_sq K
    fin_cases i
    · simp [planeToAdjoinX, Cusp.coneMap, hr]
      rfl
    · simp only [planeToAdjoinX, map_mul, Cusp.coneMap, Fin.isValue, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_zero, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X, Matrix.cons_val_fin_one]
      change rootX K * (ofX K (yX K) * ofX K (invX K) * rootX K) = ofX K (yX K)
      have hx' : ofX K (xX K) * ofX K (invX K) = 1 := by
        simpa only [map_mul, map_one] using congrArg (AdjoinRoot.of (chartRelX K)) hx
      linear_combination (ofX K (yX K) * ofX K (invX K)) * hr + ofX K (yX K) * hx'
    · simp only [planeToAdjoinX, map_mul, Cusp.coneMap, Fin.isValue, Fin.reduceFinMk,
        Matrix.cons_val, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      change (ofX K (yX K) * ofX K (invX K) * rootX K) ^ 2 = ofX K (zX K)
      have hx' : ofX K (xX K) * ofX K (invX K) = 1 := by
        simpa only [map_mul, map_one] using congrArg (AdjoinRoot.of (chartRelX K)) hx
      have hy' : ofX K (yX K) ^ 2 = ofX K (xX K) * ofX K (zX K) := by
        simpa only [map_mul, map_pow] using congrArg (AdjoinRoot.of (chartRelX K)) hy
      linear_combination (ofX K (yX K) * ofX K (invX K)) ^ 2 * hr +
        ofX K (invX K) ^ 2 * ofX K (xX K) * hy' +
        ofX K (zX K) * (ofX K (xX K) * ofX K (invX K) + 1) * hx'

theorem planeToAdjoinX_X0 : planeToAdjoinX K (MvPolynomial.X 0) = rootX K := by
  simp [planeToAdjoinX]

theorem planeToAdjoinX_X1 :
    planeToAdjoinX K (MvPolynomial.X 1) = ofX K (yX K * invX K) * rootX K := by
  simp [planeToAdjoinX]

theorem planeToAdjoinX_isUnit :
    IsUnit (planeToAdjoinX K (Cusp.coneParam K (coneX K))) := by
  rw [planeToAdjoinX_cone]
  exact (IsLocalization.Away.algebraMap_isUnit (coneX K)).map _

/-- The inverse chart: `u ↦ T`, `v ↦ yT/x`, extended to `k[u,v]_{u²}`. -/
def sourceToAdjoinX : SourceX K →+* AdjoinRoot (chartRelX K) :=
  IsLocalization.Away.lift _ (planeToAdjoinX_isUnit K)

@[simp] theorem sourceToAdjoinX_algebraMap (p : SourceRing K) :
    sourceToAdjoinX K (algebraMap (SourceRing K) (SourceX K) p) = planeToAdjoinX K p :=
  IsLocalization.Away.lift_eq _ _ p

theorem sourceToAdjoinX_comp_chartX :
    (sourceToAdjoinX K).comp (chartX K).toRingHom = AdjoinRoot.of (chartRelX K) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coneX K))
  refine RingHom.ext fun r => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom]
  rw [chartX_on_cone_coordinate, sourceToAdjoinX_algebraMap]
  exact planeToAdjoinX_cone K r

theorem adjoinToSourceX_comp_sourceToAdjoinX :
    (adjoinToSourceX K).comp (sourceToAdjoinX K) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Cusp.coneParam K (coneX K)))
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.coe_comp, Function.comp_apply, sourceToAdjoinX_algebraMap,
      RingHom.id_apply]
    simp only [planeToAdjoinX, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
      adjoinToSourceX_of, AlgHom.commutes]
    rfl
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, sourceToAdjoinX_algebraMap,
      RingHom.id_apply]
    fin_cases i
    · simp [planeToAdjoinX_X0]
    · simp only [Fin.mk_one, Fin.isValue, planeToAdjoinX_X1, map_mul, adjoinToSourceX_of,
        adjoinToSourceX_root, chartX_yX]
      have h := congrArg (chartX K) (xX_mul_invX K)
      rw [map_mul, map_one, chartX_xX] at h
      linear_combination vX K * h

theorem sourceToAdjoinX_comp_adjoinToSourceX :
    (sourceToAdjoinX K).comp (adjoinToSourceX K) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · rw [RingHom.comp_assoc, adjoinToSourceX, AdjoinRoot.lift_comp_of]
    exact sourceToAdjoinX_comp_chartX K
  · simp [planeToAdjoinX_X0]

/-- **Explicit chart over `D(x)`.** The localized source ring `k[u,v]_{u²}` is the
target localization `k[Y]_x` with a root `T` of `T²-x` adjoined; `T ↦ u`. -/
def chartEquivX : AdjoinRoot (chartRelX K) ≃ₐ[TargetX K] SourceX K :=
  { RingEquiv.ofRingHom (adjoinToSourceX K) (sourceToAdjoinX K)
      (adjoinToSourceX_comp_sourceToAdjoinX K) (sourceToAdjoinX_comp_adjoinToSourceX K) with
    commutes' := fun t => adjoinToSourceX_of K t }

@[simp] theorem chartEquivX_root : chartEquivX K (rootX K) = uX K :=
  adjoinToSourceX_root K

@[simp] theorem chartEquivX_symm_u : (chartEquivX K).symm (uX K) = rootX K := by
  rw [← chartEquivX_root, AlgEquiv.symm_apply_apply]

/-- The inverse chart recovers `v = y·T/x = y/T`. -/
theorem chartEquivX_symm_v :
    (chartEquivX K).symm (vX K) = ofX K (yX K * invX K) * rootX K :=
  (sourceToAdjoinX_algebraMap K _).trans (planeToAdjoinX_X1 K)

theorem chartEquivX_symm_v_mul_root :
    (chartEquivX K).symm (vX K) * rootX K = ofX K (yX K) := by
  rw [chartEquivX_symm_v]
  have hx' : ofX K (xX K) * ofX K (invX K) = 1 := by
    simpa only [map_mul, map_one] using congrArg (AdjoinRoot.of (chartRelX K)) (xX_mul_invX K)
  simp only [map_mul]
  linear_combination (ofX K (yX K) * ofX K (invX K)) * rootX_sq K + ofX K (yX K) * hx'

/-! ### The chart over `D(z)` -/

/-- The cone coordinate `x` in the target localization `k[Y]_z`. -/
abbrev xZ : TargetZ K := algebraMap (ConeRing K) (TargetZ K) (coneX K)
/-- The cone coordinate `y` in the target localization `k[Y]_z`. -/
abbrev yZ : TargetZ K := algebraMap (ConeRing K) (TargetZ K) (coneY K)
/-- The cone coordinate `z` in the target localization `k[Y]_z`. -/
abbrev zZ : TargetZ K := algebraMap (ConeRing K) (TargetZ K) (coneZ K)
/-- The inverse of `z` in `k[Y]_z`. -/
abbrev invZ : TargetZ K := IsLocalization.Away.invSelf (coneZ K)

theorem zZ_mul_invZ : zZ K * invZ K = 1 := IsLocalization.Away.mul_invSelf _

theorem yZ_sq : yZ K ^ 2 = xZ K * zZ K := by
  simp only [← map_pow, ← map_mul, coneY_sq]

/-- The monic relation `T² - z` over `k[Y]_z`. -/
def chartRelZ : (TargetZ K)[X] := X ^ 2 - C (zZ K)

/-- The source coordinate `u` in `k[u,v]_{v²}`. -/
abbrev uZ : SourceZ K := algebraMap (SourceRing K) (SourceZ K) (MvPolynomial.X 0)
/-- The source coordinate `v` in `k[u,v]_{v²}`. -/
abbrev vZ : SourceZ K := algebraMap (SourceRing K) (SourceZ K) (MvPolynomial.X 1)

theorem chartZ_zZ : chartZ K (zZ K) = vZ K ^ 2 :=
  (chartZ_on_cone_coordinate K _).trans
    ((congrArg (algebraMap (SourceRing K) (SourceZ K)) (coneParam_z K)).trans (map_pow _ _ _))

theorem chartZ_yZ : chartZ K (yZ K) = uZ K * vZ K := by
  rw [chartZ_on_cone_coordinate, coneParam_y, map_mul]

/-- The root `T ↦ v`. -/
def adjoinToSourceZ : AdjoinRoot (chartRelZ K) →+* SourceZ K :=
  AdjoinRoot.lift (chartZ K).toRingHom (vZ K) (by
    simp only [chartRelZ, eval₂_sub, eval₂_X_pow, eval₂_C]
    change vZ K ^ 2 - chartZ K (zZ K) = 0
    rw [chartZ_zZ, sub_self])

@[simp] theorem adjoinToSourceZ_root : adjoinToSourceZ K (AdjoinRoot.root _) = vZ K :=
  AdjoinRoot.lift_root _

@[simp] theorem adjoinToSourceZ_of (t : TargetZ K) :
    adjoinToSourceZ K (AdjoinRoot.of _ t) = chartZ K t :=
  AdjoinRoot.lift_of _

/-- The root `T` of `T² - z`. -/
abbrev rootZ : AdjoinRoot (chartRelZ K) := AdjoinRoot.root (chartRelZ K)
/-- Scalars from `k[Y]_z`. -/
abbrev ofZ (t : TargetZ K) : AdjoinRoot (chartRelZ K) := AdjoinRoot.of (chartRelZ K) t

theorem rootZ_sq : rootZ K ^ 2 = ofZ K (zZ K) := by
  have h : AdjoinRoot.mk (chartRelZ K) (X ^ 2 - C (zZ K)) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  exact h

/-- On the plane, `u ↦ yT/z` and `v ↦ T`. -/
def planeToAdjoinZ : SourceRing K →+* AdjoinRoot (chartRelZ K) :=
  MvPolynomial.eval₂Hom ((AdjoinRoot.of (chartRelZ K)).comp (algebraMap K (TargetZ K)))
    ![ofZ K (yZ K * invZ K) * rootZ K, rootZ K]

theorem planeToAdjoinZ_cone (r : ConeRing K) :
    planeToAdjoinZ K (Cusp.coneParam K r) = ofZ K (algebraMap (ConeRing K) (TargetZ K) r) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  change planeToAdjoinZ K (MvPolynomial.aeval (Cusp.coneMap K) p) = _
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [planeToAdjoinZ]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X]
    congr 1
    have hr := rootZ_sq K
    have hz' : ofZ K (zZ K) * ofZ K (invZ K) = 1 := by
      simpa only [map_mul, map_one] using congrArg (AdjoinRoot.of (chartRelZ K)) (zZ_mul_invZ K)
    have hy' : ofZ K (yZ K) ^ 2 = ofZ K (xZ K) * ofZ K (zZ K) := by
      simpa only [map_mul, map_pow] using congrArg (AdjoinRoot.of (chartRelZ K)) (yZ_sq K)
    fin_cases i
    · simp only [planeToAdjoinZ, map_mul, Cusp.coneMap, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_X]
      change (ofZ K (yZ K) * ofZ K (invZ K) * rootZ K) ^ 2 = ofZ K (xZ K)
      linear_combination (ofZ K (yZ K) * ofZ K (invZ K)) ^ 2 * hr +
        ofZ K (invZ K) ^ 2 * ofZ K (zZ K) * hy' +
        ofZ K (xZ K) * (ofZ K (zZ K) * ofZ K (invZ K) + 1) * hz'
    · simp only [planeToAdjoinZ, map_mul, Cusp.coneMap, Fin.isValue, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_zero, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X, Matrix.cons_val_fin_one]
      change ofZ K (yZ K) * ofZ K (invZ K) * rootZ K * rootZ K = ofZ K (yZ K)
      linear_combination (ofZ K (yZ K) * ofZ K (invZ K)) * hr + ofZ K (yZ K) * hz'
    · simp [planeToAdjoinZ, Cusp.coneMap, hr]
      rfl

theorem planeToAdjoinZ_X1 : planeToAdjoinZ K (MvPolynomial.X 1) = rootZ K := by
  simp [planeToAdjoinZ]

theorem planeToAdjoinZ_X0 :
    planeToAdjoinZ K (MvPolynomial.X 0) = ofZ K (yZ K * invZ K) * rootZ K := by
  simp [planeToAdjoinZ]

theorem planeToAdjoinZ_isUnit :
    IsUnit (planeToAdjoinZ K (Cusp.coneParam K (coneZ K))) := by
  rw [planeToAdjoinZ_cone]
  exact (IsLocalization.Away.algebraMap_isUnit (coneZ K)).map _

/-- The inverse chart: `v ↦ T`, `u ↦ yT/z`, extended to `k[u,v]_{v²}`. -/
def sourceToAdjoinZ : SourceZ K →+* AdjoinRoot (chartRelZ K) :=
  IsLocalization.Away.lift _ (planeToAdjoinZ_isUnit K)

@[simp] theorem sourceToAdjoinZ_algebraMap (p : SourceRing K) :
    sourceToAdjoinZ K (algebraMap (SourceRing K) (SourceZ K) p) = planeToAdjoinZ K p :=
  IsLocalization.Away.lift_eq _ _ p

theorem sourceToAdjoinZ_comp_chartZ :
    (sourceToAdjoinZ K).comp (chartZ K).toRingHom = AdjoinRoot.of (chartRelZ K) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coneZ K))
  refine RingHom.ext fun r => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom]
  rw [chartZ_on_cone_coordinate, sourceToAdjoinZ_algebraMap]
  exact planeToAdjoinZ_cone K r

theorem adjoinToSourceZ_comp_sourceToAdjoinZ :
    (adjoinToSourceZ K).comp (sourceToAdjoinZ K) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Cusp.coneParam K (coneZ K)))
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.coe_comp, Function.comp_apply, sourceToAdjoinZ_algebraMap,
      RingHom.id_apply]
    simp only [planeToAdjoinZ, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
      adjoinToSourceZ_of, AlgHom.commutes]
    rfl
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, sourceToAdjoinZ_algebraMap,
      RingHom.id_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, planeToAdjoinZ_X0, map_mul, adjoinToSourceZ_of,
        adjoinToSourceZ_root, chartZ_yZ]
      have h := congrArg (chartZ K) (zZ_mul_invZ K)
      rw [map_mul, map_one, chartZ_zZ] at h
      linear_combination uZ K * h
    · simp [planeToAdjoinZ_X1]

theorem sourceToAdjoinZ_comp_adjoinToSourceZ :
    (sourceToAdjoinZ K).comp (adjoinToSourceZ K) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · rw [RingHom.comp_assoc, adjoinToSourceZ, AdjoinRoot.lift_comp_of]
    exact sourceToAdjoinZ_comp_chartZ K
  · simp [planeToAdjoinZ_X1]

/-- **Explicit chart over `D(z)`.** The localized source ring `k[u,v]_{v²}` is the
target localization `k[Y]_z` with a root `T` of `T²-z` adjoined; `T ↦ v`. -/
def chartEquivZ : AdjoinRoot (chartRelZ K) ≃ₐ[TargetZ K] SourceZ K :=
  { RingEquiv.ofRingHom (adjoinToSourceZ K) (sourceToAdjoinZ K)
      (adjoinToSourceZ_comp_sourceToAdjoinZ K) (sourceToAdjoinZ_comp_adjoinToSourceZ K) with
    commutes' := fun t => adjoinToSourceZ_of K t }

@[simp] theorem chartEquivZ_root : chartEquivZ K (rootZ K) = vZ K :=
  adjoinToSourceZ_root K

@[simp] theorem chartEquivZ_symm_v : (chartEquivZ K).symm (vZ K) = rootZ K := by
  rw [← chartEquivZ_root, AlgEquiv.symm_apply_apply]

/-- The inverse chart recovers `u = y·T/z = y/T`. -/
theorem chartEquivZ_symm_u :
    (chartEquivZ K).symm (uZ K) = ofZ K (yZ K * invZ K) * rootZ K :=
  (sourceToAdjoinZ_algebraMap K _).trans (planeToAdjoinZ_X0 K)

theorem chartEquivZ_symm_u_mul_root :
    (chartEquivZ K).symm (uZ K) * rootZ K = ofZ K (yZ K) := by
  rw [chartEquivZ_symm_u]
  have hz' : ofZ K (zZ K) * ofZ K (invZ K) = 1 := by
    simpa only [map_mul, map_one] using congrArg (AdjoinRoot.of (chartRelZ K)) (zZ_mul_invZ K)
  simp only [map_mul]
  linear_combination (ofZ K (yZ K) * ofZ K (invZ K)) * rootZ_sq K + ofZ K (yZ K) * hz'

variable [CharZero K]

/-- The unit `x` of `k[Y]_x`. -/
def unitX : (TargetX K)ˣ := (IsLocalization.Away.algebraMap_isUnit (coneX K)).unit

/-- The unit `z` of `k[Y]_z`. -/
def unitZ : (TargetZ K)ˣ := (IsLocalization.Away.algebraMap_isUnit (coneZ K)).unit

theorem twoUnitX : IsUnit (2 : TargetX K) := by
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h2.map (algebraMap K (TargetX K))

theorem twoUnitZ : IsUnit (2 : TargetZ K) := by
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h2.map (algebraMap K (TargetZ K))

theorem chartRelX_eq :
    chartRelX K = (standardQuadraticPair
      (unitX K) (twoUnitX K)).f := rfl

instance adjoinX_etale : Algebra.Etale (TargetX K) (AdjoinRoot (chartRelX K)) :=
  Algebra.Etale.of_equiv (standardPairEquivAdjoinRoot
    (standardQuadraticPair
      (unitX K) (twoUnitX K)) rfl)

/-- The localized cone map over `D(x)` is étale, through the explicit chart. -/
theorem chartX_etale_explicit : Algebra.Etale (TargetX K) (SourceX K) :=
  Algebra.Etale.of_equiv (chartEquivX K)

/-- The actual cone morphism restricted over `D(x)` is étale. -/
theorem coneMap_restrict_basicOpen_x_etale :
    Etale (coneMap K ∣_ PrimeSpectrum.basicOpen (coneX K)) := by
  refine (MorphismProperty.arrow_mk_iso_iff (@Etale)
    (coneRestrictXIso K)).mpr ?_
  unfold schemeChartX
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  change (algebraMap (TargetX K) (SourceX K)).Etale
  exact (RingHom.etale_algebraMap).mpr (chartX_etale_explicit K)

instance adjoinZ_etale : Algebra.Etale (TargetZ K) (AdjoinRoot (chartRelZ K)) :=
  Algebra.Etale.of_equiv (standardPairEquivAdjoinRoot
    (standardQuadraticPair
      (unitZ K) (twoUnitZ K)) rfl)

/-- The localized cone map over `D(z)` is étale, through the explicit chart. -/
theorem chartZ_etale_explicit : Algebra.Etale (TargetZ K) (SourceZ K) :=
  Algebra.Etale.of_equiv (chartEquivZ K)

/-- The actual cone morphism restricted over `D(z)` is étale. -/
theorem coneMap_restrict_basicOpen_z_etale :
    Etale (coneMap K ∣_ PrimeSpectrum.basicOpen (coneZ K)) := by
  refine (MorphismProperty.arrow_mk_iso_iff (@Etale)
    (coneRestrictZIso K)).mpr ?_
  unfold schemeChartZ
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  change (algebraMap (TargetZ K) (SourceZ K)).Etale
  exact (RingHom.etale_algebraMap).mpr (chartZ_etale_explicit K)


/-! ### Normality, étale stalks off the vertex, and the empty ambient branch -/

/-- The actual cone scheme is normal. -/
instance cone_isNormal : IsNormalScheme (cone K) := by
  let : IsIntegrallyClosed (ConeRing K) := cone_isIntegrallyClosed K
  exact CharZeroPaperSmoothBranch.normal_spec (ConeRing K)

instance sourcePlane_isNormal : IsNormalScheme (sourcePlane K) :=
  CharZeroPaperSmoothBranch.normal_spec (SourceRing K)

omit [CharZero K] in
theorem coneMap_stalk_formallyEtale_of_basicOpen (r : ConeRing K)
    (hr : Etale (coneMap K ∣_ PrimeSpectrum.basicOpen r)) (q : sourcePlane K)
    (hq : coneMap K q ∈ PrimeSpectrum.basicOpen r) :
    ((coneMap K).stalkMap q).hom.FormallyEtale := by
  let f := coneMap K
  let U : (cone K).Opens := PrimeSpectrum.basicOpen r
  have hpU : q ∈ f ⁻¹ᵁ U := hq
  have hrestr : Etale (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hr
  exact (Pcf.formallyEtale_respectsIso.arrow_mk_iso_iff
    (f.resLEStalkMap le_rfl ⟨q, hpU⟩)).mp (Etale.stalkMap_formallyEtale hrestr ⟨q, hpU⟩)

/-- Off the vertex, the actual stalk maps of the cone map are formally étale;
this is deduced from the two explicit charts. -/
theorem coneMap_stalk_formallyEtale_off_vertex (q : sourcePlane K)
    (hq : coneMap K q ≠ vertex K) : ((coneMap K).stalkMap q).hom.FormallyEtale := by
  rcases mem_basicOpen_x_or_z K _ hq with h | h
  · exact coneMap_stalk_formallyEtale_of_basicOpen K _
      (coneMap_restrict_basicOpen_x_etale K) q h
  · exact coneMap_stalk_formallyEtale_of_basicOpen K _
      (coneMap_restrict_basicOpen_z_etale K) q h

/-- Stacks étaleness at every source point mapping off the vertex, from the explicit charts. -/
theorem coneMap_isStacksEtaleAt_off_vertex (q : sourcePlane K) (hq : coneMap K q ≠ vertex K) :
    Pcf.Stacks.IsStacksEtaleAt (coneMap K) q := by
  let f := coneMap K
  rcases mem_basicOpen_x_or_z K _ hq with h | h
  · let U : (cone K).Opens := PrimeSpectrum.basicOpen (coneX K)
    have : Etale (f ∣_ U) := coneMap_restrict_basicOpen_x_etale K
    have hcomp : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    exact (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
      (f := f) (f ⁻¹ᵁ U).ι ⟨q, h⟩).mp
        (Pcf.Stacks.forall_isStacksEtaleAt_iff.mpr hcomp ⟨q, h⟩)
  · let U : (cone K).Opens := PrimeSpectrum.basicOpen (coneZ K)
    have : Etale (f ∣_ U) := coneMap_restrict_basicOpen_z_etale K
    have hcomp : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    exact (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
      (f := f) (f ⁻¹ᵁ U).ι ⟨q, h⟩).mp
        (Pcf.Stacks.forall_isStacksEtaleAt_iff.mpr hcomp ⟨q, h⟩)

/-- **Étale away from the origin.** The actual cone morphism restricted over the
complement of the vertex (whose preimage is the complement of the origin) is étale. -/
theorem coneMap_restrict_punctured_etale :
    Etale (coneMap K ∣_ puncturedOpen K) := by
  let f := coneMap K
  let U := puncturedOpen K
  have : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
    apply Pcf.Stacks.forall_isStacksEtaleAt_iff.mp
    intro q
    apply (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
      (f := f) (f ⁻¹ᵁ U).ι q).mpr
    exact coneMap_isStacksEtaleAt_off_vertex K q.1 ((mem_puncturedOpen_iff_ne_vertex K _).mp q.2)
  have hcomp : Etale ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  exact Etale.of_comp (f ∣_ U) U.ι

/-- The structure morphism of the cone to the base field. -/
def coneStructure : cone K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ConeRing K)))

/-- Every source divisor has ramification index one (the dictionary of
`lem:dictionary`, applied to the explicit étale charts). -/
theorem coneMap_ramificationIdx_eq_one (Q : SchemeDivisorPoint (sourcePlane K)) :
    schemeDivisorRamificationIdx (coneMap K) Q = 1 :=
  (ramificationIdx_eq_one_iff_formallyEtale_charZero K (coneStructure K) (coneMap K) Q).mpr
    (coneMap_stalk_formallyEtale_off_vertex K Q.1 (coneMap_divisor_ne_vertex K Q))

/-- No target divisor has a nonreduced fibre. -/
theorem coneMap_reducedFiberBranch_empty : schemeReducedFiberBranch (coneMap K) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro E hE
  obtain ⟨Q, -, hQ⟩ := (mem_schemeReducedFiberBranch_iff (coneMap K) E).mp hE
  rw [coneMap_ramificationIdx_eq_one] at hQ
  exact lt_irrefl _ hQ

/-- **`branch(f) = ∅`.** The actual normalized branch locus of the cone map is empty. -/
theorem normalized_cone_branch_empty : normalizedMorphismBranchSupport (coneMap K) = ∅ := by
  rw [CharZeroPaperSmoothBranch.normalized_support_eq_reduced_support,
    coneMap_reducedFiberBranch_empty]
  simp [divisorSupport]

/-! ### The vertex has codimension two -/

omit [CharZero K] in
theorem targetLineIdeal_lt_vertex : targetLineIdeal K < (vertex K).asIdeal := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [targetLineIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact vertex_coordinates K 1
    · exact vertex_coordinates K 2
  · intro h
    have hx : coneX K ∈ targetLineIdeal K := h ▸ vertex_coordinates K 0
    rw [← targetLinePullback_ker, RingHom.mem_ker] at hx
    change (MvPolynomial.aeval ![(X : K[X]), 0, 0]) (MvPolynomial.X 0) = 0 at hx
    simp at hx

omit [CharZero K] in
/-- The cone ring has Krull dimension at most two. -/
theorem cone_ringKrullDim_le : ringKrullDim (ConeRing K) + 1 ≤ 3 := by
  have hr : (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2 :
      MvPolynomial (Fin 3) K) ∈ nonZeroDivisors _ := by
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro h0
    have h := congrArg (MvPolynomial.eval ![(1 : K), 0, 1]) h0
    simp at h
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact h

omit [CharZero K] in
/-- The target line `V(y,z)` is not the zero ideal. -/
theorem targetLineIdeal_ne_bot : targetLineIdeal K ≠ ⊥ := by
  intro h
  have hz : coneZ K ∈ targetLineIdeal K := Ideal.subset_span (Or.inr rfl)
  rw [h, Ideal.mem_bot] at hz
  have := congrArg (Cusp.coneParam K) hz
  rw [coneParam_z, map_zero] at this
  exact pow_ne_zero 2 (MvPolynomial.X_ne_zero 1) this

/-- **Codimension two.** The vertex prime has height exactly two. -/
theorem vertex_height : (vertex K).asIdeal.height = 2 := by
  have hB : 1 ≤ (targetLineIdeal K).height := by
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact targetLineIdeal_ne_bot K (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (targetLineIdeal_lt_vertex K)
  apply le_antisymm
  · have h := Ideal.height_le_ringKrullDim_of_isPrime (I := (vertex K).asIdeal)
    have h3 := cone_ringKrullDim_le K
    have h4 : ((vertex K).asIdeal.height : WithBot ℕ∞) + 1 ≤ ringKrullDim (ConeRing K) + 1 := by
      gcongr
    have h5 := h4.trans h3
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_ofNat (α := ℕ∞) 3] at h5
    have hle' : (vertex K).asIdeal.height + 1 ≤ 3 := WithBot.coe_le_coe.mp h5
    cases hv : (vertex K).asIdeal.height using ENat.recTopCoe with
    | top => rw [hv] at hle'; simp at hle'
    | coe n =>
      rw [hv] at hle'
      have : n + 1 ≤ 3 := by exact_mod_cast hle'
      exact_mod_cast (by omega : n ≤ 2)
  · calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (targetLineIdeal K).height + 1 := by gcongr
      _ ≤ _ := hlt

/-- The target line `B = V(y,z)` is an integral effective divisor of the cone. -/
theorem targetLineIdeal_height : (targetLineIdeal K).height = 1 := by
  have hB : 1 ≤ (targetLineIdeal K).height := by
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact targetLineIdeal_ne_bot K (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (targetLineIdeal_lt_vertex K)
  rw [vertex_height] at hlt
  apply le_antisymm _ hB
  cases hv : (targetLineIdeal K).height using ENat.recTopCoe with
  | top => rw [hv] at hlt; simp at hlt
  | coe n =>
    rw [hv] at hlt
    have : n + 1 ≤ 2 := by exact_mod_cast hlt
    exact_mod_cast (by omega : n ≤ 1)

/-- The vertex, as a scheme point of the cone, has codimension two. -/
theorem vertex_coheight : Order.coheight (vertex K) = 2 :=
  (AlgebraicGeometry.idealHeight_eq_coheight (.of (ConeRing K)) (vertex K)).symm.trans
    (vertex_height K)

/-- The vertex is not the generic point of an integral effective divisor. -/
theorem vertex_not_divisor : Order.coheight (vertex K) ≠ 1 := by
  rw [vertex_coheight]
  decide


/-! ### The vertex is singular

The local ring at the vertex surjects onto `k ⊕ k³` with square-zero `k³`;
hence its maximal ideal needs three generators, while its dimension is two. -/

/-- The first-order thickening `k ⊕ k³` of the vertex. -/
abbrev VertexJet := TrivSqZeroExt K (Fin 3 → K)

/-- The first-order Taylor expansion at the vertex. -/
def vertexJet : ConeRing K →ₐ[K] VertexJet K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun i => TrivSqZeroExt.inr (Pi.single i 1)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [TrivSqZeroExt.inr_mul_inr, pow_two])

omit [CharZero K] in
theorem vertexJet_fst (r : ConeRing K) : (vertexJet K r).fst = vertexEval K r := by
  have h : (TrivSqZeroExt.fstHom K K (Fin 3 → K)).comp (vertexJet K) = vertexEval K := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [vertexJet, vertexEval, targetLinePullback]
  exact congrArg (fun g : ConeRing K →ₐ[K] K => g r) h

omit [CharZero K] in
theorem vertexJet_inr (v : Fin 3 → K) :
    vertexJet K (Ideal.Quotient.mk _ (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i)) =
      TrivSqZeroExt.inr v := by
  simp only [vertexJet, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, map_sum, map_mul,
    RingHom.coe_coe, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr]
  rw [← TrivSqZeroExt.inr_sum]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

omit [CharZero K] in
theorem vertexJet_inr_mem (v : Fin 3 → K) :
    Ideal.Quotient.mk _ (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) ∈ (vertex K).asIdeal := by
  rw [mem_vertex_iff, ← vertexJet_fst, vertexJet_inr]
  rfl

/-- The local ring of the cone at its vertex. -/
abbrev VertexLocalRing := Localization.AtPrime (vertex K).asIdeal

omit [CharZero K] in
theorem vertexJet_isUnit (s : (vertex K).asIdeal.primeCompl) :
    IsUnit ((vertexJet K).toRingHom s) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.isUnit_iff_isUnit_fst,
    vertexJet_fst, isUnit_iff_ne_zero]
  exact fun h => s.2 ((mem_vertex_iff K _).mpr h)

/-- The first-order jet map from the local ring at the vertex. -/
def localJet : VertexLocalRing K →+* VertexJet K :=
  IsLocalization.lift (M := (vertex K).asIdeal.primeCompl) (vertexJet_isUnit K)

omit [CharZero K] in
@[simp] theorem localJet_algebraMap (r : ConeRing K) :
    localJet K (algebraMap (ConeRing K) (VertexLocalRing K) r) = vertexJet K r :=
  IsLocalization.lift_eq _ _

omit [CharZero K] in
theorem maximalIdeal_eq_ker_fst :
    IsLocalRing.maximalIdeal (VertexLocalRing K) =
      RingHom.ker ((TrivSqZeroExt.fstHom K K (Fin 3 → K)).toRingHom.comp (localJet K)) := by
  symm
  apply IsLocalRing.eq_maximalIdeal
  refine RingHom.ker_isMaximal_of_surjective (R := VertexLocalRing K) (K := K)
    ((TrivSqZeroExt.fstHom K K (Fin 3 → K)).toRingHom.comp (localJet K)) ?_
  intro a
  refine ⟨algebraMap (ConeRing K) (VertexLocalRing K) (algebraMap K (ConeRing K) a), ?_⟩
  simp

omit [CharZero K] in
/-- The maximal ideal of the local ring at the vertex needs at least three generators. -/
theorem three_le_spanFinrank_vertex :
    3 ≤ (IsLocalRing.maximalIdeal (VertexLocalRing K)).spanFinrank := by
  let L := VertexLocalRing K
  let m := IsLocalRing.maximalIdeal L
  have hfg : m.FG := IsNoetherian.noetherian m
  obtain ⟨S, hcard, hspan⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  have hSfin : S.Finite := Set.finite_of_encard_eq_coe hcard
  let W : Set (Fin 3 → K) := TrivSqZeroExt.snd '' (localJet K '' S)
  have hWfin : W.Finite := (hSfin.image _).image _
  have hfst : ∀ t ∈ m, (localJet K t).fst = 0 := by
    intro t ht
    rw [show m = _ from maximalIdeal_eq_ker_fst K, RingHom.mem_ker] at ht
    exact ht
  have hA : ∀ w ∈ Ideal.span (localJet K '' S), w.fst = 0 ∧ w.snd ∈ Submodule.span K W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t, ht, rfl⟩ := hw
      exact ⟨hfst t (hspan ▸ Submodule.subset_span ht),
        Submodule.subset_span ⟨_, ⟨t, ht, rfl⟩, rfl⟩⟩
    | zero => exact ⟨rfl, Submodule.zero_mem _⟩
    | add a b _ _ ha hb =>
      exact ⟨by simp [ha.1, hb.1], by simpa using Submodule.add_mem _ ha.2 hb.2⟩
    | smul c a _ ha =>
      refine ⟨by simp [smul_eq_mul, ha.1], ?_⟩
      simp only [smul_eq_mul, TrivSqZeroExt.snd_mul, ha.1, MulOpposite.op_zero, zero_smul,
        add_zero]
      exact Submodule.smul_mem _ _ ha.2
  have htop : Submodule.span K W = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hmem : algebraMap (ConeRing K) L
        (Ideal.Quotient.mk _ (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i)) ∈ m :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L (vertex K).asIdeal _).mpr
        (vertexJet_inr_mem K v)
    rw [← hspan] at hmem
    have himg := Ideal.mem_map_of_mem (localJet K) hmem
    rw [Ideal.map_span, localJet_algebraMap, vertexJet_inr] at himg
    exact (hA _ himg).2
  have hrank : Module.finrank K (Submodule.span K W) ≤ W.ncard :=
    finrank_span_le_ncard W hWfin
  rw [htop, finrank_top, Module.finrank_fin_fun] at hrank
  have hW : W.ncard ≤ S.ncard :=
    (Set.ncard_image_le (hSfin.image _)).trans (Set.ncard_image_le hSfin)
  have hS : S.ncard = (IsLocalRing.maximalIdeal (VertexLocalRing K)).spanFinrank := by
    have h := hSfin.cast_ncard_eq
    rw [hcard] at h
    exact_mod_cast h
  omega

/-- **The vertex is a singular point.** -/
theorem vertex_not_regular : ¬ IsRegularLocalRing (VertexLocalRing K) := by
  intro h
  have h1 := h.spanFinrank_maximalIdeal
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (vertex K).asIdeal (VertexLocalRing K),
    vertex_height] at h1
  have h3 := three_le_spanFinrank_vertex K
  have h2 : (IsLocalRing.maximalIdeal (VertexLocalRing K)).spanFinrank = 2 := by
    exact_mod_cast h1
  omega


/-! ### Off the vertex the cone is regular

On `D(x)` the cone is `k[a,b]_a` with `x = a`, `y = b`, `z = b²/a`; on `D(z)`
it is `k[a,b]_a` with `z = a`, `y = b`, `x = b²/a`. -/

/-- The localized plane `k[a,b]_a`. -/
abbrev AwayPlane := Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)

abbrev aB : AwayPlane K := algebraMap (MvPolynomial (Fin 2) K) (AwayPlane K) (MvPolynomial.X 0)
abbrev bB : AwayPlane K := algebraMap (MvPolynomial (Fin 2) K) (AwayPlane K) (MvPolynomial.X 1)
abbrev invB : AwayPlane K := IsLocalization.Away.invSelf (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)

omit [CharZero K] in
theorem aB_mul_invB : aB K * invB K = 1 := IsLocalization.Away.mul_invSelf _

instance awayPlane_isRegularRing : IsRegularRing (AwayPlane K) :=
  isRegularRing_of_isLocalization
    (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)) (AwayPlane K)

/-- A prime avoiding `r` has a regular local ring when `R_r` is a regular ring. -/
theorem isRegularLocalRing_of_away {R : Type u} [CommRing R] (r : R) (S : Type u) [CommRing S]
    [Algebra R S] [IsLocalization.Away r S] [IsRegularRing S] (p : Ideal R) [p.IsPrime]
    (hr : r ∉ p) : IsRegularLocalRing (Localization.AtPrime p) := by
  let q := p.map (algebraMap R S)
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers r) S p inferInstance
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hr)
  have hq : q.comap (algebraMap R S) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers r) S inferInstance
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hr)
  have h := (isRegularLocalRing_localizationAtPrime_iff (.powers r) S q).mp inferInstance
  have key : ∀ (I : Ideal R) [I.IsPrime], I = q.comap (algebraMap R S) →
      IsRegularLocalRing (Localization.AtPrime I) := by
    intro I _ hI
    subst hI
    exact h
  exact key p hq.symm

omit [CharZero K] in
theorem coneRelation_mul (c : MvPolynomial (Fin 3) K) (A : Type u) [CommRing A] [Algebra K A]
    (w : Fin 3 → A) (hw : w 0 * w 2 = w 1 ^ 2) :
    MvPolynomial.aeval w ((MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) * c) =
      0 := by
  simp [hw]

/-- `x ↦ a`, `y ↦ b`, `z ↦ b²/a`. -/
def coneToAwayPlaneX : ConeRing K →ₐ[K] AwayPlane K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![aB K, bB K, bB K ^ 2 * invB K]) (by
    intro t ht
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ht
    apply coneRelation_mul
    change aB K * (bB K ^ 2 * invB K) = bB K ^ 2
    linear_combination bB K ^ 2 * aB_mul_invB K)

omit [CharZero K] in
theorem coneToAwayPlaneX_x : coneToAwayPlaneX K (coneX K) = aB K := by
  simp [coneToAwayPlaneX, coneX]

omit [CharZero K] in
theorem coneToAwayPlaneX_y : coneToAwayPlaneX K (coneY K) = bB K := by
  simp [coneToAwayPlaneX, coneY]

/-- The inverse direction `a ↦ x`, `b ↦ y`. -/
def planeToTargetX : MvPolynomial (Fin 2) K →ₐ[K] TargetX K :=
  MvPolynomial.aeval ![xX K, yX K]

omit [CharZero K] in
theorem coneToAwayPlaneX_isUnit : IsUnit (coneToAwayPlaneX K (coneX K)) := by
  rw [coneToAwayPlaneX_x]; exact IsLocalization.Away.algebraMap_isUnit _

omit [CharZero K] in
theorem planeToTargetX_X0 : planeToTargetX K (MvPolynomial.X 0) = xX K := by
  rw [planeToTargetX, MvPolynomial.aeval_X]; rfl

omit [CharZero K] in
theorem planeToTargetX_X1 : planeToTargetX K (MvPolynomial.X 1) = yX K := by
  rw [planeToTargetX, MvPolynomial.aeval_X]; rfl

omit [CharZero K] in
theorem planeToTargetX_isUnit : IsUnit (planeToTargetX K (MvPolynomial.X 0)) := by
  rw [planeToTargetX_X0]; exact IsLocalization.Away.algebraMap_isUnit _

def targetXToAwayPlane : TargetX K →ₐ[K] AwayPlane K :=
  IsLocalization.Away.liftAlgHom (coneX K) (coneToAwayPlaneX_isUnit K)

def awayPlaneToTargetX : AwayPlane K →ₐ[K] TargetX K :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X 0) (planeToTargetX_isUnit K)

omit [CharZero K] in
@[simp] theorem targetXToAwayPlane_algebraMap (r : ConeRing K) :
    targetXToAwayPlane K (algebraMap (ConeRing K) (TargetX K) r) = coneToAwayPlaneX K r :=
  IsLocalization.Away.lift_eq _ (coneToAwayPlaneX_isUnit K) r

omit [CharZero K] in
@[simp] theorem awayPlaneToTargetX_algebraMap (r : MvPolynomial (Fin 2) K) :
    awayPlaneToTargetX K (algebraMap _ (AwayPlane K) r) = planeToTargetX K r :=
  IsLocalization.Away.lift_eq _ (planeToTargetX_isUnit K) r

omit [CharZero K] in
theorem awayPlaneToTargetX_invB : xX K * awayPlaneToTargetX K (invB K) = 1 := by
  have h := congrArg (awayPlaneToTargetX K) (aB_mul_invB K)
  rw [map_mul, map_one, awayPlaneToTargetX_algebraMap] at h
  simpa [planeToTargetX] using h

omit [CharZero K] in
theorem targetXToAwayPlane_comp :
    (targetXToAwayPlane K).comp (awayPlaneToTargetX K) = AlgHom.id K _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) K))
  apply MvPolynomial.algHom_ext
  intro i
  change targetXToAwayPlane K (awayPlaneToTargetX K (algebraMap _ _ (MvPolynomial.X i))) =
    algebraMap _ _ (MvPolynomial.X i)
  rw [awayPlaneToTargetX_algebraMap]
  fin_cases i <;>
    simp [planeToTargetX, coneToAwayPlaneX, coneX, coneY]

omit [CharZero K] in
theorem awayPlaneToTargetX_comp :
    (awayPlaneToTargetX K).comp (targetXToAwayPlane K) = AlgHom.id K _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coneX K))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hinv := awayPlaneToTargetX_invB K
  have hy := yX_sq K
  change awayPlaneToTargetX K (targetXToAwayPlane K (algebraMap (ConeRing K) _
    (Ideal.Quotient.mk _ (MvPolynomial.X i)))) =
    algebraMap (ConeRing K) _ (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [targetXToAwayPlane_algebraMap]
  fin_cases i
  · change awayPlaneToTargetX K (coneToAwayPlaneX K (coneX K)) = xX K
    rw [coneToAwayPlaneX_x, awayPlaneToTargetX_algebraMap, planeToTargetX_X0]
  · change awayPlaneToTargetX K (coneToAwayPlaneX K (coneY K)) = yX K
    rw [coneToAwayPlaneX_y, awayPlaneToTargetX_algebraMap, planeToTargetX_X1]
  · change awayPlaneToTargetX K (coneToAwayPlaneX K (Ideal.Quotient.mk _ (MvPolynomial.X 2))) =
      zX K
    simp only [coneToAwayPlaneX, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
      RingHom.coe_coe, MvPolynomial.aeval_X]
    have hb : awayPlaneToTargetX K (bB K) = yX K := by
      rw [awayPlaneToTargetX_algebraMap, planeToTargetX_X1]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_mul, map_pow, hb]
    linear_combination awayPlaneToTargetX K (invB K) * hy + zX K * hinv

/-- `k[Y]_x ≅ k[a,b]_a`. -/
def targetXEquiv : TargetX K ≃ₐ[K] AwayPlane K :=
  AlgEquiv.ofAlgHom (targetXToAwayPlane K) (awayPlaneToTargetX K)
    (targetXToAwayPlane_comp K) (awayPlaneToTargetX_comp K)

instance targetX_isRegularRing : IsRegularRing (TargetX K) :=
  IsRegularRing.of_ringEquiv (targetXEquiv K).symm.toRingEquiv

/-- `x ↦ b²/a`, `y ↦ b`, `z ↦ a`. -/
def coneToAwayPlaneZ : ConeRing K →ₐ[K] AwayPlane K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![bB K ^ 2 * invB K, bB K, aB K]) (by
    intro t ht
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ht
    apply coneRelation_mul
    change bB K ^ 2 * invB K * aB K = bB K ^ 2
    linear_combination bB K ^ 2 * aB_mul_invB K)

omit [CharZero K] in
theorem coneToAwayPlaneZ_z : coneToAwayPlaneZ K (coneZ K) = aB K := by
  simp [coneToAwayPlaneZ, coneZ]

omit [CharZero K] in
theorem coneToAwayPlaneZ_y : coneToAwayPlaneZ K (coneY K) = bB K := by
  simp [coneToAwayPlaneZ, coneY]

/-- The inverse direction `a ↦ z`, `b ↦ y`. -/
def planeToTargetZ : MvPolynomial (Fin 2) K →ₐ[K] TargetZ K :=
  MvPolynomial.aeval ![zZ K, yZ K]

omit [CharZero K] in
theorem coneToAwayPlaneZ_isUnit : IsUnit (coneToAwayPlaneZ K (coneZ K)) := by
  rw [coneToAwayPlaneZ_z]; exact IsLocalization.Away.algebraMap_isUnit _

omit [CharZero K] in
theorem planeToTargetZ_X0 : planeToTargetZ K (MvPolynomial.X 0) = zZ K := by
  rw [planeToTargetZ, MvPolynomial.aeval_X]; rfl

omit [CharZero K] in
theorem planeToTargetZ_X1 : planeToTargetZ K (MvPolynomial.X 1) = yZ K := by
  rw [planeToTargetZ, MvPolynomial.aeval_X]; rfl

omit [CharZero K] in
theorem planeToTargetZ_isUnit : IsUnit (planeToTargetZ K (MvPolynomial.X 0)) := by
  rw [planeToTargetZ_X0]; exact IsLocalization.Away.algebraMap_isUnit _

def targetZToAwayPlane : TargetZ K →ₐ[K] AwayPlane K :=
  IsLocalization.Away.liftAlgHom (coneZ K) (coneToAwayPlaneZ_isUnit K)

def awayPlaneToTargetZ : AwayPlane K →ₐ[K] TargetZ K :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X 0) (planeToTargetZ_isUnit K)

omit [CharZero K] in
@[simp] theorem targetZToAwayPlane_algebraMap (r : ConeRing K) :
    targetZToAwayPlane K (algebraMap (ConeRing K) (TargetZ K) r) = coneToAwayPlaneZ K r :=
  IsLocalization.Away.lift_eq _ (coneToAwayPlaneZ_isUnit K) r

omit [CharZero K] in
@[simp] theorem awayPlaneToTargetZ_algebraMap (r : MvPolynomial (Fin 2) K) :
    awayPlaneToTargetZ K (algebraMap _ (AwayPlane K) r) = planeToTargetZ K r :=
  IsLocalization.Away.lift_eq _ (planeToTargetZ_isUnit K) r

omit [CharZero K] in
theorem awayPlaneToTargetZ_invB : zZ K * awayPlaneToTargetZ K (invB K) = 1 := by
  have h := congrArg (awayPlaneToTargetZ K) (aB_mul_invB K)
  rw [map_mul, map_one, awayPlaneToTargetZ_algebraMap] at h
  simpa [planeToTargetZ] using h

omit [CharZero K] in
theorem targetZToAwayPlane_comp :
    (targetZToAwayPlane K).comp (awayPlaneToTargetZ K) = AlgHom.id K _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) K))
  apply MvPolynomial.algHom_ext
  intro i
  change targetZToAwayPlane K (awayPlaneToTargetZ K (algebraMap _ _ (MvPolynomial.X i))) =
    algebraMap _ _ (MvPolynomial.X i)
  rw [awayPlaneToTargetZ_algebraMap]
  fin_cases i <;>
    simp [planeToTargetZ, coneToAwayPlaneZ, coneZ, coneY]

omit [CharZero K] in
theorem awayPlaneToTargetZ_comp :
    (awayPlaneToTargetZ K).comp (targetZToAwayPlane K) = AlgHom.id K _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coneZ K))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hinv := awayPlaneToTargetZ_invB K
  have hy := yZ_sq K
  change awayPlaneToTargetZ K (targetZToAwayPlane K (algebraMap (ConeRing K) _
    (Ideal.Quotient.mk _ (MvPolynomial.X i)))) =
    algebraMap (ConeRing K) _ (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [targetZToAwayPlane_algebraMap]
  fin_cases i
  · change awayPlaneToTargetZ K (coneToAwayPlaneZ K (Ideal.Quotient.mk _ (MvPolynomial.X 0))) =
      xZ K
    simp only [coneToAwayPlaneZ, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
      RingHom.coe_coe, MvPolynomial.aeval_X]
    have hb : awayPlaneToTargetZ K (bB K) = yZ K := by
      rw [awayPlaneToTargetZ_algebraMap, planeToTargetZ_X1]
    simp only [Matrix.cons_val_zero, map_mul, map_pow, hb]
    linear_combination awayPlaneToTargetZ K (invB K) * hy + xZ K * hinv
  · change awayPlaneToTargetZ K (coneToAwayPlaneZ K (coneY K)) = yZ K
    rw [coneToAwayPlaneZ_y, awayPlaneToTargetZ_algebraMap, planeToTargetZ_X1]
  · change awayPlaneToTargetZ K (coneToAwayPlaneZ K (coneZ K)) = zZ K
    rw [coneToAwayPlaneZ_z, awayPlaneToTargetZ_algebraMap, planeToTargetZ_X0]

/-- `k[Y]_z ≅ k[a,b]_a`. -/
def targetZEquiv : TargetZ K ≃ₐ[K] AwayPlane K :=
  AlgEquiv.ofAlgHom (targetZToAwayPlane K) (awayPlaneToTargetZ K)
    (targetZToAwayPlane_comp K) (awayPlaneToTargetZ_comp K)

instance targetZ_isRegularRing : IsRegularRing (TargetZ K) :=
  IsRegularRing.of_ringEquiv (targetZEquiv K).symm.toRingEquiv

omit [CharZero K] in
/-- Every point other than the vertex has a regular local ring. -/
theorem regular_off_vertex (p : cone K) (hp : p ≠ vertex K) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  rcases mem_basicOpen_x_or_z K p hp with h | h
  · exact isRegularLocalRing_of_away (coneX K) (TargetX K) p.asIdeal h
  · exact isRegularLocalRing_of_away (coneZ K) (TargetZ K) p.asIdeal h

/-- **`Sing(Y) = {o}`.** The pointwise singular locus of the actual cone is its vertex. -/
theorem cone_singularLocus : stalkSingularLocus (cone K) = {vertex K} := by
  rw [stalkSingularLocus_Spec_eq]
  ext p
  simp only [Set.mem_compl_iff, primeRegularLocus, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hp
    by_contra hne
    exact hp (regular_off_vertex K p hne)
  · rintro rfl
    exact vertex_not_regular K


/-! ### The whole example -/

/-- The cone ring is the ring of invariants of `(u,v) ↦ (-u,-v)`. -/
theorem coneParam_range_invariants (p : SourceRing K) :
    negBoth K p = p ↔ ∃ a, Cusp.coneParam K a = p :=
  negBoth_fixed_iff K p

/-- The cone map is étale (on stalks) at every point except the origin. -/
theorem coneMap_stalk_formallyEtale_off_origin (q : sourcePlane K)
    (hq : q ≠ planeOrigin K) :
    ((coneMap K).stalkMap q).hom.FormallyEtale := by
  apply coneMap_stalk_formallyEtale_off_vertex K q
  intro h
  have : q ∈ coneMap K ⁻¹' {vertex K} := h
  rw [coneMap_preimage_vertex] at this
  exact hq this

/-- `B ∩ branch(f) = ∅`; hence `B ∩ Z = ∅` for every `Z ⊆ branch(f)`. -/
theorem targetLine_inter_cone_branch_empty :
    Set.range (targetLine K) ∩ normalizedMorphismBranchSupport (coneMap K) = ∅ := by
  rw [normalized_cone_branch_empty, Set.inter_empty]

/-- The restricted branch point is not in `B ∩ branch(f)`. -/
theorem restricted_branch_not_subset :
    ¬ targetLine K '' normalizedMorphismBranchSupport (squareMap K) ⊆
      Set.range (targetLine K) ∩ normalizedMorphismBranchSupport (coneMap K) := by
  rw [restricted_branch_image, targetLine_inter_cone_branch_empty]
  simp

/-- The restricted branch point lies on `B ∩ Sing(Y)`. -/
theorem restricted_branch_subset_singular :
    targetLine K '' normalizedMorphismBranchSupport (squareMap K) ⊆
      (Set.range (targetLine K) ∩ normalizedMorphismBranchSupport (coneMap K)) ∪
        (Set.range (targetLine K) ∩ stalkSingularLocus (cone K)) := by
  rw [restricted_branch_image, cone_singularLocus]
  rintro _ rfl
  exact Or.inr ⟨⟨_, rfl⟩, rfl⟩

/-- **`ex:branch-singular`.** The quadric cone `Y = Spec k[x,y,z]/(xz-y²)` is normal
and singular only at its vertex `o`, which has codimension two. The map
`f(u,v) = (u²,uv,v²)` presents `Y` as the quotient of the plane by `±1`; it is finite
and surjective, étale over the complement of the vertex (so away from the origin),
which is the only point over `o`, and
`branch(f) = ∅`. For `A = V(v)` and `B = V(y,z)` the restriction is `g(u) = u²`,
`branch(g) = {o}`, while `B ∩ branch(f) = ∅`; the branch point lies on `B ∩ Sing(Y)`.

Manuscript: `ex:branch-singular` (Example 6.7), `rem:branch-bound-sharpness` (Remark 6.9). -/
theorem ex_branch_singular :
    IsNormalScheme (cone K) ∧
    stalkSingularLocus (cone K) = {vertex K} ∧
    Order.coheight (vertex K) = 2 ∧
    Function.Injective (Cusp.coneParam K) ∧
    (∀ p : SourceRing K,
      negBoth K p = p ↔ ∃ a, Cusp.coneParam K a = p) ∧
    IsFinite (coneMap K) ∧ Surjective (coneMap K) ∧
    (∀ p : cone K, p ∈ puncturedOpen K ↔ p ≠ vertex K) ∧
    Etale (coneMap K ∣_ puncturedOpen K) ∧
    (∀ q : sourcePlane K, q ≠ planeOrigin K →
      ((coneMap K).stalkMap q).hom.FormallyEtale) ∧
    coneMap K ⁻¹' {vertex K} = {planeOrigin K} ∧
    normalizedMorphismBranchSupport (coneMap K) = ∅ ∧
    Set.range (sourceLine K) = PrimeSpectrum.zeroLocus {(MvPolynomial.X 1 : SourceRing K)} ∧
    Set.range (targetLine K) =
      PrimeSpectrum.zeroLocus {coneY K, coneZ K} ∧
    sourceLine K ≫ coneMap K = squareMap K ≫ targetLine K ∧
    targetLine K '' normalizedMorphismBranchSupport (squareMap K) = {vertex K} ∧
    Set.range (targetLine K) ∩ normalizedMorphismBranchSupport (coneMap K) = ∅ ∧
    ¬ targetLine K '' normalizedMorphismBranchSupport (squareMap K) ⊆
      Set.range (targetLine K) ∩ normalizedMorphismBranchSupport (coneMap K) ∧
    targetLine K '' normalizedMorphismBranchSupport (squareMap K) ⊆
      (Set.range (targetLine K) ∩ normalizedMorphismBranchSupport (coneMap K)) ∪
        (Set.range (targetLine K) ∩ stalkSingularLocus (cone K)) :=
  ⟨inferInstance, cone_singularLocus K, vertex_coheight K, coneParam_injective K,
    coneParam_range_invariants K, inferInstance, inferInstance,
    mem_puncturedOpen_iff_ne_vertex K, coneMap_restrict_punctured_etale K,
    coneMap_stalk_formallyEtale_off_origin K, coneMap_preimage_vertex K,
    normalized_cone_branch_empty K, sourceLine_range K, targetLine_range K,
    restriction_square K, restricted_branch_image K, targetLine_inter_cone_branch_empty K,
    restricted_branch_not_subset K, restricted_branch_subset_singular K⟩

end Pcf.Examples.CharZeroPaperConeBranch

#print axioms Pcf.Examples.CharZeroPaperConeBranch.xX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.yX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.zX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.invX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.xX_mul_invX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.yX_sq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartRelX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.uX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartX_xX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartX_yX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceX_root
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceX_of
#print axioms Pcf.Examples.CharZeroPaperConeBranch.rootX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.ofX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.rootX_sq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinX_cone
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinX_X0
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinX_X1
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinX_isUnit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinX_algebraMap
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinX_comp_chartX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceX_comp_sourceToAdjoinX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinX_comp_adjoinToSourceX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivX_root
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivX_symm_u
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivX_symm_v
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivX_symm_v_mul_root
#print axioms Pcf.Examples.CharZeroPaperConeBranch.xZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.yZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.zZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.invZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.zZ_mul_invZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.yZ_sq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartRelZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.uZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartZ_zZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartZ_yZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceZ_root
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceZ_of
#print axioms Pcf.Examples.CharZeroPaperConeBranch.rootZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.ofZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.rootZ_sq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinZ_cone
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinZ_X1
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinZ_X0
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToAdjoinZ_isUnit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinZ_algebraMap
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinZ_comp_chartZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinToSourceZ_comp_sourceToAdjoinZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToAdjoinZ_comp_adjoinToSourceZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivZ_root
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivZ_symm_v
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivZ_symm_u
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartEquivZ_symm_u_mul_root
#print axioms Pcf.Examples.CharZeroPaperConeBranch.unitX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.unitZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.twoUnitX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.twoUnitZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartRelX_eq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinX_etale
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartX_etale_explicit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_restrict_basicOpen_x_etale
#print axioms Pcf.Examples.CharZeroPaperConeBranch.adjoinZ_etale
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartZ_etale_explicit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_restrict_basicOpen_z_etale
#print axioms Pcf.Examples.CharZeroPaperConeBranch.cone_isNormal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourcePlane_isNormal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_stalk_formallyEtale_of_basicOpen
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_stalk_formallyEtale_off_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_isStacksEtaleAt_off_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_restrict_punctured_etale
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneStructure
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_ramificationIdx_eq_one
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_reducedFiberBranch_empty
#print axioms Pcf.Examples.CharZeroPaperConeBranch.normalized_cone_branch_empty
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLineIdeal_lt_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.cone_ringKrullDim_le
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLineIdeal_ne_bot
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertex_height
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLineIdeal_height
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertex_coheight
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertex_not_divisor
#print axioms Pcf.Examples.CharZeroPaperConeBranch.VertexJet
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexJet
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexJet_fst
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexJet_inr
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexJet_inr_mem
#print axioms Pcf.Examples.CharZeroPaperConeBranch.VertexLocalRing
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexJet_isUnit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.localJet
#print axioms Pcf.Examples.CharZeroPaperConeBranch.localJet_algebraMap
#print axioms Pcf.Examples.CharZeroPaperConeBranch.maximalIdeal_eq_ker_fst
#print axioms Pcf.Examples.CharZeroPaperConeBranch.three_le_spanFinrank_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertex_not_regular
#print axioms Pcf.Examples.CharZeroPaperConeBranch.AwayPlane
#print axioms Pcf.Examples.CharZeroPaperConeBranch.aB
#print axioms Pcf.Examples.CharZeroPaperConeBranch.bB
#print axioms Pcf.Examples.CharZeroPaperConeBranch.invB
#print axioms Pcf.Examples.CharZeroPaperConeBranch.aB_mul_invB
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlane_isRegularRing
#print axioms Pcf.Examples.CharZeroPaperConeBranch.isRegularLocalRing_of_away
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneRelation_mul
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneX_x
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneX_y
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneX_isUnit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetX_X0
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetX_X1
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetX_isUnit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetXToAwayPlane
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetXToAwayPlane_algebraMap
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetX_algebraMap
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetX_invB
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetXToAwayPlane_comp
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetX_comp
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetXEquiv
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetX_isRegularRing
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneZ_z
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneZ_y
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneToAwayPlaneZ_isUnit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetZ_X0
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetZ_X1
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeToTargetZ_isUnit
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetZToAwayPlane
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetZToAwayPlane_algebraMap
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetZ_algebraMap
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetZ_invB
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetZToAwayPlane_comp
#print axioms Pcf.Examples.CharZeroPaperConeBranch.awayPlaneToTargetZ_comp
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetZEquiv
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetZ_isRegularRing
#print axioms Pcf.Examples.CharZeroPaperConeBranch.regular_off_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.cone_singularLocus
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_range_invariants
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_stalk_formallyEtale_off_origin
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLine_inter_cone_branch_empty
#print axioms Pcf.Examples.CharZeroPaperConeBranch.restricted_branch_not_subset
#print axioms Pcf.Examples.CharZeroPaperConeBranch.restricted_branch_subset_singular
#print axioms Pcf.Examples.CharZeroPaperConeBranch.ex_branch_singular
