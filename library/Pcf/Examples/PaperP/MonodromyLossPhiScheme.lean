/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiA
public import Pcf.Examples.PaperP.MonodromyLossCurveRegular

/-!
# `φ = 1 + ι : E ⟶ E` as a morphism of schemes (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss` (Part II), char 3, `i² = -1`:

* `phiB : Spec B ⟶ E`, glued from `D(w)` (through `Spec B[1/w] ≅ Spec A[1/y]` and `phiA`)
  and `D(1 - ws) ∋ O` (`phi3`). The generic-point identity is checked in `Frac B` by
  `QB_hK_true` and `fid1`.
* `phi_compat`, and **`phi : E ⟶ E`** (`desc`), `ιA_phi`, `ιB_phi`, `phi_D_x` (the explicit
  formula on `D(x)`), and `phi_toSpec` (`φ` is a `k`-morphism).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

theorem fid1 {F : Type*} [Field F] (S W c : F) (_hS : S ≠ 0) (hW : W ≠ 0)
    (hE : 1 - W * S ≠ 0) (hB : S ^ 3 = W ^ 2 * S + W) (hc : c ^ 2 = -1) (h3 : (3 : F) = 0) :
    -(1 + c) * W⁻¹ * ((S * W⁻¹) ^ 2 + 1) * (S * W⁻¹)⁻¹ ^ 2 * ((1 - c) * S ^ 3 * (1 - W * S)⁻¹)
      = 1 := by
  field_simp
  linear_combination S * (S ^ 2 + W ^ 2) * hc - 2 * hB - (W ^ 2 * S + W) * h3

section PhiB
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

omit [CharP k 3] in
theorem eB_ne_zero : eB k ≠ 0 := by
  intro h
  have := congrArg (liftB k (0 : k) 0 (by ring)) h
  simp [eB, liftB_s, liftB_w] at this

/-- The cover `D(w) ∪ D(1 - ws)` of the chart at infinity. -/
noncomputable def sBB : Idx.{u} → B k
  | ⟨false⟩ => wB k
  | ⟨true⟩ => eB k

omit [CharP k 3] in
theorem sBB_span : Ideal.span (Set.range (sBB k)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hw : wB k ∈ Ideal.span (Set.range (sBB k)) := Ideal.subset_span ⟨⟨false⟩, rfl⟩
  have he : eB k ∈ Ideal.span (Set.range (sBB k)) := Ideal.subset_span ⟨⟨true⟩, rfl⟩
  have : (1 : B k) = eB k + sB k * wB k := by ring
  rw [this]
  exact Ideal.add_mem _ he (Ideal.mul_mem_left _ _ hw)

omit [CharP k 3] in
theorem sBB_ne_zero : ∀ j, sBB k j ≠ 0
  | ⟨false⟩ => wB_ne_zero k
  | ⟨true⟩ => eB_ne_zero k

theorem phiA_toSpec : phiA k i hi ≫ toSpec k = Spec.map (CommRingCat.ofHom (algebraMap k (A k))) :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of (A k)) (sA k) (sA_span k)).openCover.hom_ext
    _ _ fun j => by
      have := SpecMap_glueGeneric (sA k) (sA_span k) (sA_ne_zero k) (toSpec k)
        (Spec.map (CommRingCat.ofHom (algebraMap k (A k)))) (gKA k i hi) (PA k i hi)
        (PA_hZ k i hi) (PA_hK k i hi) j
      change Spec.map _ ≫ phiA k i hi ≫ toSpec k = Spec.map _ ≫ _
      rw [← Category.assoc]
      unfold phiA
      rw [this, PA_hZ]

/-- The pieces of `φ` on the chart at infinity. -/
noncomputable def QB : ∀ j, Spec (.of (Localization.Away (sBB k j))) ⟶ E k
  | ⟨false⟩ => Spec.map (CommRingCat.ofHom (AyToBw k)) ≫ jA k ≫ phiA k i hi
  | ⟨true⟩ => Spec.map (CommRingCat.ofHom (phi3 k i hi)) ≫ ιB k

/-- The generic point of `φ` on the chart at infinity. -/
noncomputable def gKB : Spec (.of (FractionRing (B k))) ⟶ E k :=
  Spec.map (CommRingCat.ofHom ((awayToK (wB k) (wB_ne_zero k)).comp (AyToBw k))) ≫ jA k ≫
    phiA k i hi

theorem phi3_algebraMap (r : k) : phi3 k i hi (algebraMap k (B k) r) = algebraMap k (Be k) r :=
  liftB_algebraMap k _ _ _ r

omit [CharP k 3] in
theorem AyToBw_algebraMap_k (r : k) :
    AyToBw k (algebraMap (A k) (Ay k) (algebraMap k (A k) r)) = algebraMap k (Bw k) r := by
  rw [AyToBw_algebraMap, AtoBw, liftA_algebraMap]

set_option backward.isDefEq.respectTransparency true in
theorem QB_hZ (j : Idx.{u}) : QB k i hi j ≫ toSpec k =
    Spec.map (CommRingCat.ofHom (algebraMap (B k) (Localization.Away (sBB k j)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (B k))) := by
  rcases j with ⟨_ | _⟩
  · change Spec.map _ ≫ jA k ≫ phiA k i hi ≫ toSpec k = _
    rw [phiA_toSpec, jA, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext r
    change AyToBw k (algebraMap (A k) (Ay k) (algebraMap k (A k) r)) =
      algebraMap (B k) (Bw k) (algebraMap k (B k) r)
    rw [AyToBw_algebraMap_k, ← IsScalarTower.algebraMap_apply]
  · change Spec.map _ ≫ ιB k ≫ toSpec k = _
    rw [ιB_toSpec, ← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext r
    change phi3 k i hi (algebraMap k (B k) r) = algebraMap (B k) (Be k) (algebraMap k (B k) r)
    rw [phi3_algebraMap, ← IsScalarTower.algebraMap_apply]

omit [CharP k 3] in
theorem awayToK_algebraMap_kB (s : B k) (hs : s ≠ 0) (r : k) :
    awayToK s hs (algebraMap k (Localization.Away s) r) = algebraMap k (FractionRing (B k)) r := by
  rw [IsScalarTower.algebraMap_apply k (B k) (Localization.Away s), awayToK_algebraMap,
    ← IsScalarTower.algebraMap_apply]

set_option backward.isDefEq.respectTransparency true in
theorem QB_hK_true :
    Spec.map (CommRingCat.ofHom ((awayToK (eB k) (eB_ne_zero k)).comp (phi3 k i hi))) ≫ ιB k =
      gKB k i hi := by
  set K := FractionRing (B k)
  set S := algebraMap (B k) K (sB k)
  set W := algebraMap (B k) K (wB k)
  set c := algebraMap k K i
  let ρ : Ay k →+* K := (awayToK (wB k) (wB_ne_zero k)).comp (AyToBw k)
  have hinj : Function.Injective (algebraMap (B k) K) := IsFractionRing.injective _ _
  have hS : S ≠ 0 := fun h => sB_ne_zero k (hinj (h.trans (map_zero _).symm))
  have hW : W ≠ 0 := fun h => wB_ne_zero k (hinj (h.trans (map_zero _).symm))
  have hE : 1 - W * S ≠ 0 := fun h => eB_ne_zero k (hinj (by simpa [eB, S, W] using h))
  have hWi : awayToK (wB k) (wB_ne_zero k) (invW k) = W⁻¹ := by
    have := congrArg (awayToK (wB k) (wB_ne_zero k)) (w_mul_invW k)
    rw [map_mul, map_one, awayToK_algebraMap] at this
    exact eq_inv_of_mul_eq_one_right this
  have hEi : awayToK (eB k) (eB_ne_zero k) (invE k) = (1 - W * S)⁻¹ := by
    have := congrArg (awayToK (eB k) (eB_ne_zero k))
      (IsLocalization.Away.mul_invSelf (S := Be k) (eB k))
    rw [map_mul, map_one, awayToK_algebraMap] at this
    simpa [eB, S, W] using eq_inv_of_mul_eq_one_right this
  have hρx : ρ (algebraMap (A k) (Ay k) (xA k)) = S * W⁻¹ := by
    simp only [ρ, RingHom.comp_apply, AyToBw_algebraMap, AtoBw, liftA_x, map_mul,
      awayToK_algebraMap, hWi]
    rfl
  have hρy : ρ (algebraMap (A k) (Ay k) (yA k)) = W⁻¹ := by
    simp only [ρ, RingHom.comp_apply, AyToBw_algebraMap, AtoBw, liftA_y, hWi]
  have hux : IsUnit ((ρ.comp (algebraMap (A k) (Ay k))) (xA k)) := by
    rw [RingHom.comp_apply, hρx]; exact (mul_ne_zero hS (inv_ne_zero hW)).isUnit
  let α' : Ax k →+* K := IsLocalization.Away.lift (xA k) hux
  have hα' : α'.comp (algebraMap (A k) (Ax k)) = ρ.comp (algebraMap (A k) (Ay k)) :=
    IsLocalization.Away.lift_comp _ _
  have hα'a (a : A k) : α' (algebraMap (A k) (Ax k) a) = ρ (algebraMap (A k) (Ay k) a) :=
    congrArg (· a) hα'
  have hXi : α' (invX k) = (S * W⁻¹)⁻¹ := by
    have := congrArg α' (IsLocalization.Away.mul_invSelf (S := Ax k) (xA k))
    rw [map_mul, map_one, hα'a, hρx] at this
    exact eq_inv_of_mul_eq_one_right this
  have e1 : gKB k i hi = Spec.map (CommRingCat.ofHom (α'.comp (phi1 k i hi))) ≫ ιA k := by
    rw [gKB, jA, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (ρ.comp (algebraMap (A k) (Ay k)))) ≫ _ = _
    rw [← hα', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, phiA_D_x,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e1]
  symm
  have hB : S ^ 3 = W ^ 2 * S + W := by
    have := congrArg (algebraMap (B k) K) (B_rel k); simpa using this
  have hc : c ^ 2 = -1 := by
    have := congrArg (algebraMap k K) hi; simpa using this
  have h3 := three_eq_zero k K
  have hα'c (r : k) : α' (algebraMap k (Ax k) r) = algebraMap k K r := by
    rw [IsScalarTower.algebraMap_apply k (A k) (Ax k), hα'a]
    simp only [ρ, RingHom.comp_apply]
    rw [AyToBw_algebraMap_k, awayToK_algebraMap_kB]
  have hSdef : algebraMap (B k) (FractionRing (B k)) (sB k) = S := rfl
  have hWdef : algebraMap (B k) (FractionRing (B k)) (wB k) = W := rfl
  have hcdef : algebraMap k (FractionRing (B k)) i = c := rfl
  have hcdef' : algebraMap k K i = c := rfl
  have hE' : 1 - S * W ≠ 0 := by rwa [mul_comm]
  apply SpecMap_ιA_eq_ιB k
  · intro r
    rw [RingHom.comp_apply, phi1_algebraMap, hα'c]
  · intro r
    rw [RingHom.comp_apply, phi3_algebraMap, awayToK_algebraMap_kB]
  · simp only [RingHom.comp_apply, phi1, phi3, liftA_y, liftB_w, map_mul, map_neg, map_add,
      map_sub, map_pow, map_one, hα'a, hρx, hρy, hXi, hEi, awayToK_algebraMap, hα'c,
      awayToK_algebraMap_kB, hSdef, hcdef, hcdef']
    exact fid1 S W c hS hW hE hB hc h3
  · simp only [RingHom.comp_apply, phi1, phi3, liftA_x, liftB_s, liftB_w, map_mul, map_add,
      map_sub, map_pow, map_one, hα'a, hρx, hXi, hEi, awayToK_algebraMap, hα'c,
      awayToK_algebraMap_kB, hSdef, hcdef, hcdef']
    field_simp
    linear_combination (-(1 + c)) * hB + (S * (S ^ 2 - W ^ 2)) * hc

set_option backward.isDefEq.respectTransparency true in
theorem QB_hK (j : Idx.{u}) :
    Spec.map (CommRingCat.ofHom (awayToK (sBB k j) (sBB_ne_zero k j))) ≫ QB k i hi j =
      gKB k i hi := by
  rcases j with ⟨_ | _⟩
  · change Spec.map _ ≫ Spec.map _ ≫ jA k ≫ phiA k i hi = Spec.map _ ≫ jA k ≫ phiA k i hi
    rw [← Category.assoc, ← Spec.map_comp]; rfl
  · change Spec.map _ ≫ Spec.map _ ≫ ιB k = _
    rw [← Category.assoc, ← Spec.map_comp]
    exact QB_hK_true k i hi

/-- **`φ` on the chart at infinity**, `Spec B ⟶ E`, glued from `D(w)` (through the overlap
and `phiA`) and `D(1 - ws) ∋ O` (`phi3`). -/
noncomputable def phiB : Spec (.of (B k)) ⟶ E k :=
  glueGeneric (sBB k) (sBB_span k) (sBB_ne_zero k) (toSpec k)
    (Spec.map (CommRingCat.ofHom (algebraMap k (B k)))) (gKB k i hi) (QB k i hi)
    (QB_hZ k i hi) (QB_hK k i hi)

set_option backward.isDefEq.respectTransparency true in
theorem phiB_D_w : Spec.map (CommRingCat.ofHom (algebraMap (B k) (Bw k))) ≫ phiB k i hi =
    Spec.map (CommRingCat.ofHom (AyToBw k)) ≫ jA k ≫ phiA k i hi :=
  SpecMap_glueGeneric (sBB k) (sBB_span k) (sBB_ne_zero k) (toSpec k)
    (Spec.map (CommRingCat.ofHom (algebraMap k (B k)))) (gKB k i hi) (QB k i hi)
    (QB_hZ k i hi) (QB_hK k i hi) ⟨false⟩

set_option backward.isDefEq.respectTransparency true in
theorem phiB_D_e : Spec.map (CommRingCat.ofHom (algebraMap (B k) (Be k))) ≫ phiB k i hi =
    Spec.map (CommRingCat.ofHom (phi3 k i hi)) ≫ ιB k :=
  SpecMap_glueGeneric (sBB k) (sBB_span k) (sBB_ne_zero k) (toSpec k)
    (Spec.map (CommRingCat.ofHom (algebraMap k (B k)))) (gKB k i hi) (QB k i hi)
    (QB_hZ k i hi) (QB_hK k i hi) ⟨true⟩

set_option backward.isDefEq.respectTransparency true in
theorem phi_compat : jA k ≫ phiA k i hi = jB k ≫ phiB k i hi := by
  have h : jB k = Spec.map (CommRingCat.ofHom (BwToAy k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (B k) (Bw k))) := by
    rw [jB, ← Spec.map_comp, ← CommRingCat.ofHom_comp, BwToAy_comp_algebraMap]
  rw [h, Category.assoc, phiB_D_w, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, BwToAy_comp_AyToBw, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

/-- **`φ = 1 + ι : E ⟶ E`** as an actual morphism of schemes (char 3, `i² = -1`). On the
finite chart away from `x = 0` it is `(x, y) ↦ (i(x² - 1)/x, -(1 + i) y (x² + 1)/x²)`. -/
noncomputable def phi : E k ⟶ E k :=
  desc k (phiA k i hi) (phiB k i hi) (phi_compat k i hi)

theorem ιA_phi : ιA k ≫ phi k i hi = phiA k i hi := ιA_desc k _ _ _
theorem ιB_phi : ιB k ≫ phi k i hi = phiB k i hi := ιB_desc k _ _ _

/-- On `D(x)` in the finite chart, `φ` is the chart map `phi1`. -/
theorem phi_D_x : Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ax k))) ≫ ιA k ≫ phi k i hi =
    Spec.map (CommRingCat.ofHom (phi1 k i hi)) ≫ ιA k := by
  rw [ιA_phi, phiA_D_x]

theorem phi_toSpec : phi k i hi ≫ toSpec k = toSpec k := by
  apply hom_ext k
  · rw [← Category.assoc, ιA_phi, phiA_toSpec, ιA_toSpec]
  · rw [← Category.assoc, ιB_phi, ιB_toSpec]
    refine (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of (B k)) (sBB k)
      (sBB_span k)).openCover.hom_ext _ _ fun j => ?_
    have := SpecMap_glueGeneric (sBB k) (sBB_span k) (sBB_ne_zero k) (toSpec k)
      (Spec.map (CommRingCat.ofHom (algebraMap k (B k)))) (gKB k i hi) (QB k i hi)
      (QB_hZ k i hi) (QB_hK k i hi) j
    change Spec.map _ ≫ phiB k i hi ≫ toSpec k = Spec.map _ ≫ _
    rw [← Category.assoc]
    unfold phiB
    rw [this, QB_hZ]

end PhiB

#print axioms phi
#print axioms phi_D_x
#print axioms phi_toSpec

end Pcf.Examples.PaperP.MonodromyLossCurve
