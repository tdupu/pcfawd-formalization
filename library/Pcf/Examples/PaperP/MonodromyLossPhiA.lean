/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhi

/-!
# `φ = 1 + ι` on the finite chart of `E` (`ex:monodromy-loss`)

`phiA : Spec A ⟶ E` is glued (`glueGeneric`) from `D(x) → U_A` (`phi1`) and
`D(x⁴ - 1) → U_B` (`phi2`). The two pieces are compared at the generic point
(`PA_hK_true`, an identity in `Frac A`) through `SpecMap_ιA_eq_ιB`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

section
variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency true in
/-- Two chart points of `E` agree when the finite-chart point has `y` invertible and the
chart-at-infinity point has coordinates `s = x/y`, `w = 1/y`. -/
theorem SpecMap_ιA_eq_ιB {T : Type u} [CommRing T] [Algebra k T] (a : A k →+* T)
    (b : B k →+* T) (ha : ∀ r : k, a (algebraMap k (A k) r) = algebraMap k T r)
    (hb : ∀ r : k, b (algebraMap k (B k) r) = algebraMap k T r)
    (hw : a (yA k) * b (wB k) = 1) (hs : b (sB k) = a (xA k) * b (wB k)) :
    Spec.map (CommRingCat.ofHom a) ≫ ιA k = Spec.map (CommRingCat.ofHom b) ≫ ιB k := by
  have hu : IsUnit (a (yA k)) := IsUnit.of_mul_eq_one _ hw
  let ψ : Ay k →+* T := IsLocalization.Away.lift (yA k) hu
  have h1 : ψ.comp (algebraMap (A k) (Ay k)) = a := IsLocalization.Away.lift_comp _ _
  have hψy : ψ (invY k) = b (wB k) := by
    have e1 : ψ (invY k) * a (yA k) = 1 := by
      rw [← congrArg (· (yA k)) h1, RingHom.comp_apply, ← map_mul, mul_comm, y_mul_invY,
        map_one]
    calc ψ (invY k) = ψ (invY k) * (a (yA k) * b (wB k)) := by rw [hw, mul_one]
      _ = b (wB k) := by rw [← mul_assoc, e1, one_mul]
  have h2 : ψ.comp (BtoAy k) = b := by
    apply B_ringHom_ext k
    · intro r
      refine ⟨?_, hb r⟩
      rw [RingHom.comp_apply, BtoAy, liftB_algebraMap, IsScalarTower.algebraMap_apply k (A k),
        ← RingHom.comp_apply ψ, h1, ha]
    · rw [RingHom.comp_apply, BtoAy, liftB_s, map_mul, hψy, ← RingHom.comp_apply ψ, h1, hs]
    · rw [RingHom.comp_apply, BtoAy, liftB_w, hψy]
  have e1 : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom ψ) ≫ jA k := by
    rw [jA, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h1]
  have e2 : Spec.map (CommRingCat.ofHom b) = Spec.map (CommRingCat.ofHom ψ) ≫ jB k := by
    rw [jB, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h2]
  rw [e1, e2, Category.assoc, Category.assoc, (isPullback_charts k).w]

end

section PhiA
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

omit [CharP k 3] in
theorem A_of_injective : Function.Injective (AdjoinRoot.of (W k).polynomial) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [W_polynomial k, degree_X_pow_sub_C (by norm_num)]; decide)

omit [CharP k 3] in
theorem xA_ne_zero : xA k ≠ 0 := fun h =>
  X_ne_zero (A_of_injective k (h.trans (map_zero _).symm))

omit [CharP k 3] in
theorem qA_ne_zero : qA k ≠ 0 := by
  intro h
  have : AdjoinRoot.of (W k).polynomial (X ^ 4 - C 1) = 0 := by
    rw [map_sub, map_pow, map_one, ← h]; rfl
  exact X_pow_sub_C_ne_zero (by norm_num) _ (A_of_injective k (this.trans (map_zero _).symm))

omit [CharP k 3] in
theorem awayToK_algebraMap {R : Type u} [CommRing R] [IsDomain R] (s : R) (hs : s ≠ 0) (r : R) :
    awayToK s hs (algebraMap R _ r) = algebraMap R (FractionRing R) r :=
  congrArg (· r) (awayToK_comp s hs)

/-- The basic-open cover `D(x) ∪ D(x⁴ - 1)` of the finite chart. -/
noncomputable def sA : Idx.{u} → A k
  | ⟨false⟩ => xA k
  | ⟨true⟩ => qA k

omit [CharP k 3] in
theorem sA_span : Ideal.span (Set.range (sA k)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hx : xA k ∈ Ideal.span (Set.range (sA k)) := Ideal.subset_span ⟨⟨false⟩, rfl⟩
  have hq : qA k ∈ Ideal.span (Set.range (sA k)) := Ideal.subset_span ⟨⟨true⟩, rfl⟩
  have : (1 : A k) = xA k ^ 3 * xA k - qA k := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx) hq

omit [CharP k 3] in
theorem sA_ne_zero : ∀ j, sA k j ≠ 0
  | ⟨false⟩ => xA_ne_zero k
  | ⟨true⟩ => qA_ne_zero k

/-- The pieces of `φ` on the finite chart. -/
noncomputable def PA : ∀ j, Spec (.of (Localization.Away (sA k j))) ⟶ E k
  | ⟨false⟩ => Spec.map (CommRingCat.ofHom (phi1 k i hi)) ≫ ιA k
  | ⟨true⟩ => Spec.map (CommRingCat.ofHom (phi2 k i hi)) ≫ ιB k

/-- The generic point of `φ` on the finite chart. -/
noncomputable def gKA : Spec (.of (FractionRing (A k))) ⟶ E k :=
  Spec.map (CommRingCat.ofHom ((awayToK (xA k) (xA_ne_zero k)).comp (phi1 k i hi))) ≫ ιA k

theorem phi1_algebraMap (r : k) : phi1 k i hi (algebraMap k (A k) r) = algebraMap k (Ax k) r :=
  liftA_algebraMap k _ _ _ r

theorem phi2_algebraMap (r : k) : phi2 k i hi (algebraMap k (B k) r) = algebraMap k (Aq k) r :=
  liftB_algebraMap k _ _ _ r

set_option backward.isDefEq.respectTransparency true in
theorem PA_hZ (j : Idx.{u}) : PA k i hi j ≫ toSpec k =
    Spec.map (CommRingCat.ofHom (algebraMap (A k) (Localization.Away (sA k j)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (A k))) := by
  rcases j with ⟨_ | _⟩
  · change Spec.map _ ≫ ιA k ≫ toSpec k = _
    rw [ιA_toSpec, ← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext r
    change phi1 k i hi (algebraMap k (A k) r) = algebraMap (A k) _ (algebraMap k (A k) r)
    rw [phi1_algebraMap, ← IsScalarTower.algebraMap_apply]
  · change Spec.map _ ≫ ιB k ≫ toSpec k = _
    rw [ιB_toSpec, ← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext r
    change phi2 k i hi (algebraMap k (B k) r) = algebraMap (A k) (Aq k) (algebraMap k (A k) r)
    rw [phi2_algebraMap, ← IsScalarTower.algebraMap_apply]

omit [CharP k 3] in
theorem awayToK_algebraMap_k (s : A k) (hs : s ≠ 0) (r : k) :
    awayToK s hs (algebraMap k (Localization.Away s) r) = algebraMap k (FractionRing (A k)) r := by
  rw [IsScalarTower.algebraMap_apply k (A k) (Localization.Away s), awayToK_algebraMap,
    ← IsScalarTower.algebraMap_apply]

theorem PA_hK_true :
    Spec.map (CommRingCat.ofHom ((awayToK (qA k) (qA_ne_zero k)).comp (phi2 k i hi))) ≫ ιB k =
      gKA k i hi := by
  symm
  set K := FractionRing (A k)
  set X := algebraMap (A k) K (xA k)
  set Y := algebraMap (A k) K (yA k)
  set c := algebraMap k K i
  set U := awayToK (xA k) (xA_ne_zero k) (invX k)
  set V := awayToK (qA k) (qA_ne_zero k) (invQ k)
  have hu : X * U = 1 := by
    have := congrArg (awayToK (xA k) (xA_ne_zero k)) (IsLocalization.Away.mul_invSelf
      (S := Ax k) (xA k))
    rwa [map_mul, map_one, awayToK_algebraMap] at this
  have hv : (X ^ 4 - 1) * V = 1 := by
    have := congrArg (awayToK (qA k) (qA_ne_zero k)) (IsLocalization.Away.mul_invSelf
      (S := Aq k) (qA k))
    rwa [map_mul, map_one, awayToK_algebraMap, map_sub, map_pow, map_one] at this
  have hy : Y ^ 2 = X ^ 3 - X := by
    have := congrArg (algebraMap (A k) K) (A_rel k); simpa using this
  have hc : c ^ 2 = -1 := by
    have := congrArg (algebraMap k K) hi; simpa using this
  have h3 := three_eq_zero k K
  apply SpecMap_ιA_eq_ιB k
  · intro r
    rw [RingHom.comp_apply, phi1_algebraMap, awayToK_algebraMap_k]
  · intro r
    rw [RingHom.comp_apply, phi2_algebraMap, awayToK_algebraMap_k]
  · simp only [RingHom.comp_apply, phi1, phi2, liftA_y, liftB_w, map_mul, map_neg, map_add,
      map_sub, map_pow, map_one, awayToK_algebraMap, awayToK_algebraMap_k]
    linear_combination (U*V*X^2*Y^2*c^2 - U*V*X^2*Y^2 + U*V*Y^2*c^2 - U*V*Y^2 + V*X^2*c^2 - V*X^2
        + V*X*Y^2*c^2 - V*X*Y^2 - V*c^2 + V) * hu + (c^2 - 1) * hv + (U*V*c^2 - U*V + V*X*c^2 -
        V*X) * hy + (1) * hc + (-1) * h3
  · simp only [RingHom.comp_apply, phi1, phi2, liftA_x, liftB_s, liftB_w, map_mul, map_add,
      map_sub, map_pow, map_one, awayToK_algebraMap, awayToK_algebraMap_k]
    linear_combination (V*X^2*Y*c^2 - V*X^2*Y*c - V*Y*c^2 + V*Y*c) * hu + (0) * hv + (0) * hy +
        (V*X^2*Y - V*Y) * hc + (0) * h3

set_option backward.isDefEq.respectTransparency true in
theorem PA_hK (j : Idx.{u}) :
    Spec.map (CommRingCat.ofHom (awayToK (sA k j) (sA_ne_zero k j))) ≫ PA k i hi j =
      gKA k i hi := by
  rcases j with ⟨_ | _⟩
  · change Spec.map _ ≫ Spec.map _ ≫ ιA k = Spec.map _ ≫ ιA k
    rw [← Category.assoc, ← Spec.map_comp]; rfl
  · change Spec.map _ ≫ Spec.map _ ≫ ιB k = _
    rw [← Category.assoc, ← Spec.map_comp]
    exact PA_hK_true k i hi

/-- **`φ` on the finite chart**, `Spec A ⟶ E`, glued from `D(x) → U_A` and
`D(x⁴ - 1) → U_B`. -/
noncomputable def phiA : Spec (.of (A k)) ⟶ E k :=
  glueGeneric (sA k) (sA_span k) (sA_ne_zero k) (toSpec k)
    (Spec.map (CommRingCat.ofHom (algebraMap k (A k)))) (gKA k i hi) (PA k i hi)
    (PA_hZ k i hi) (PA_hK k i hi)

set_option backward.isDefEq.respectTransparency true in
theorem phiA_D_x : Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ax k))) ≫ phiA k i hi =
    Spec.map (CommRingCat.ofHom (phi1 k i hi)) ≫ ιA k :=
  SpecMap_glueGeneric (sA k) (sA_span k) (sA_ne_zero k) (toSpec k)
    (Spec.map (CommRingCat.ofHom (algebraMap k (A k)))) (gKA k i hi) (PA k i hi)
    (PA_hZ k i hi) (PA_hK k i hi) ⟨false⟩

set_option backward.isDefEq.respectTransparency true in
theorem phiA_D_q : Spec.map (CommRingCat.ofHom (algebraMap (A k) (Aq k))) ≫ phiA k i hi =
    Spec.map (CommRingCat.ofHom (phi2 k i hi)) ≫ ιB k :=
  SpecMap_glueGeneric (sA k) (sA_span k) (sA_ne_zero k) (toSpec k)
    (Spec.map (CommRingCat.ofHom (algebraMap k (A k)))) (gKA k i hi) (PA k i hi)
    (PA_hZ k i hi) (PA_hK k i hi) ⟨true⟩

end PhiA

#print axioms phiA
#print axioms phiA_D_x
#print axioms phiA_D_q

end Pcf.Examples.PaperP.MonodromyLossCurve
