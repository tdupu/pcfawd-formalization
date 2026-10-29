/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossProductIntegral

/-!
# The sections `0, ∞` of `ℙ¹` and `z ↦ 1/z` (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: `F(P, z) = (φ(P), 1/z)` swaps `E × {0}` and
`E × {∞}`.

* `awayEval_comp_formsAwayMapTo`: evaluation at a point after homogeneous substitution is
  evaluation at the substituted point.
* `pointP1 j x`: the `k`-point of `ℙ¹` given by `x ∈ k²` with `x_j ≠ 0`, on the chart `D₊(X_j)`;
  `zeroPt = [0 : 1]`, `infPt = [1 : 0]` (coordinates `[u : v]`, `z = u / v`).
* **`zeroPt_inv`**, **`infPt_inv`**: `inv` swaps `0` and `∞`.
* **`inv_inv`**: `inv ≫ inv = 𝟙`.
* `zeroPt_structureMap`, `infPt_structureMap`: they are sections of `ℙ¹ → Spec k`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossProductSections

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section General

variable {k : Type u} [Field k] {T : Type u} [CommRing T] [Algebra k T]

/-- Evaluation after homogeneous substitution by the forms `F` is evaluation at `F(x)`. -/
theorem awayEval_comp_formsAwayMapTo (F : Index → Coordinates k) (d : ℕ)
    (hF : ∀ j, (F j).IsHomogeneous d) (P Q : Coordinates k) (hQ : Q = aeval F P)
    (x : Index → T) (h : IsUnit (aeval x Q)) (x' : Index → T)
    (hx' : x' = fun j => aeval x (F j)) (h' : IsUnit (aeval x' P)) :
    (awayEval Q x h).comp (Pcf.paperPFormsAwayMapTo F d hF P Q hQ) = awayEval P x' h' := by
  subst hx'
  ext z
  simp only [awayEval, RingHom.comp_apply]
  change IsLocalization.Away.lift Q h (Pcf.paperPFormsAwayMapTo F d hF P Q hQ z).val =
    IsLocalization.Away.lift P h' z.val
  rw [Pcf.paperPFormsAwayMapTo, Pcf.paperPDegreeLocalizationMap_val]
  generalize z.val = w
  have key : ∀ ψ : Localization.Away P →+* Localization.Away Q,
      ψ.comp (algebraMap (Coordinates k) _) =
        (algebraMap (Coordinates k) _).comp (aeval F).toRingHom →
      (IsLocalization.Away.lift Q (S := Localization.Away Q) h).comp ψ =
        IsLocalization.Away.lift P (S := Localization.Away P) h' := by
    intro ψ hψ
    refine IsLocalization.ringHom_ext (Submonoid.powers P) (RingHom.ext fun a => ?_)
    have := DFunLike.congr_fun hψ a
    simp only [RingHom.comp_apply] at this ⊢
    rw [this, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    exact MvPolynomial.comp_aeval_apply (f := F) (aeval x) a
  exact DFunLike.congr_fun (key _ (IsLocalization.map_comp _)) w

end General

variable (k : Type u) [Field k]

local notation "uu" => (X (Sum.inl 0) : Coordinates k)
local notation "vv" => (X (Sum.inr ()) : Coordinates k)
local notation "P1" => Proj (grading k)

/-- The `k`-point `[x]` of `ℙ¹`, on the chart `D₊(X_j)` where `x_j` is a unit. -/
noncomputable def pointP1 (j : Index) (x : Index → k) (h : IsUnit (aeval x (X j : Coordinates k))) :
    Spec (.of k) ⟶ P1 :=
  Spec.map (CommRingCat.ofHom (awayEval (X j) x h)) ≫
    Proj.awayι (grading k) (X j) (isHomogeneous_X k j) Nat.zero_lt_one

/-- `[0 : 1]` (`u = 0`). -/
def x0 : Index → k := Sum.elim (fun _ => 0) (fun _ => 1)
/-- `[1 : 0]` (`v = 0`). -/
def xInf : Index → k := Sum.elim (fun _ => 1) (fun _ => 0)

theorem x0_v : IsUnit (aeval (x0 k) vv) := by simp [x0]
theorem xInf_u : IsUnit (aeval (xInf k) uu) := by simp [xInf]

/-- **The point `0 ∈ ℙ¹`.** -/
noncomputable def zeroPt : Spec (.of k) ⟶ P1 := pointP1 k (Sum.inr ()) (x0 k) (x0_v k)

/-- **The point `∞ ∈ ℙ¹`.** -/
noncomputable def infPt : Spec (.of k) ⟶ P1 := pointP1 k (Sum.inl 0) (xInf k) (xInf_u k)

/-- `inv` on a `k`-point given by coordinates. -/
theorem pointP1_inv (j j' : Index) (hj : invForms k j' = (X j : Coordinates k)) (x x' : Index → k)
    (h : IsUnit (aeval x (X j : Coordinates k))) (hx' : x' = fun l => aeval x (invForms k l))
    (h' : IsUnit (aeval x' (X j' : Coordinates k))) :
    pointP1 k j x h ≫ inv k = pointP1 k j' x' h' := by
  have hQ : (X j : Coordinates k) =
      aeval (invForms k) (X j' : Coordinates k) := by rw [aeval_X, hj]
  have sq := Pcf.paperPForms_awayι_comp_mapTo (invForms k) 1 (invForms_homogeneous k)
    (by decide) (invForms_cover k) Nat.zero_lt_one (X j' : Coordinates k) (X j : Coordinates k)
    (isHomogeneous_X k j') hQ
  rw [pointP1, pointP1, Category.assoc]
  erw [sq]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    awayEval_comp_formsAwayMapTo (invForms k) 1 (invForms_homogeneous k) _ _ hQ x h x' hx' h']

/-- **`inv` sends `0` to `∞`.** -/
theorem zeroPt_inv : zeroPt k ≫ inv k = infPt k :=
  pointP1_inv k _ _ rfl _ _ _ (by funext l; rcases l with _ | _ <;> simp [x0, xInf, invForms]) _

/-- **`inv` sends `∞` to `0`.** -/
theorem infPt_inv : infPt k ≫ inv k = zeroPt k :=
  pointP1_inv k _ _ rfl _ _ _ (by funext l; rcases l with _ | _ <;> simp [x0, xInf, invForms]) _


/-- Double homogeneous substitution by `invForms` is the identity on each chart. -/
theorem formsAwayMapTo_inv_inv (j j' : Index)
    (h1 : (X j : Coordinates k) = aeval (invForms k) (X j'))
    (h2 : (X j' : Coordinates k) = aeval (invForms k) (X j)) :
    (Pcf.paperPFormsAwayMapTo (invForms k) 1 (invForms_homogeneous k) _ _ h2).comp
      (Pcf.paperPFormsAwayMapTo (invForms k) 1 (invForms_homogeneous k) _ _ h1) =
      RingHom.id _ := by
  ext z
  simp only [RingHom.comp_apply, RingHom.id_apply, Pcf.paperPFormsAwayMapTo,
    Pcf.paperPDegreeLocalizationMap_val]
  generalize z.val = w
  have key : ∀ (ψ₁ : Localization.Away (X j' : Coordinates k) →+*
        Localization.Away (X j : Coordinates k))
      (ψ₂ : Localization.Away (X j : Coordinates k) →+* Localization.Away (X j' : Coordinates k)),
      ψ₁.comp (algebraMap (Coordinates k) _) =
        (algebraMap (Coordinates k) _).comp (aeval (invForms k)).toRingHom →
      ψ₂.comp (algebraMap (Coordinates k) _) =
        (algebraMap (Coordinates k) _).comp (aeval (invForms k)).toRingHom →
      ∀ w, ψ₂ (ψ₁ w) = w := by
    intro ψ₁ ψ₂ hψ₁ hψ₂
    suffices hh : ψ₂.comp ψ₁ = RingHom.id _ from fun w => DFunLike.congr_fun hh w
    refine IsLocalization.ringHom_ext (Submonoid.powers (X j' : Coordinates k))
      (RingHom.ext fun a => ?_)
    have e1 := DFunLike.congr_fun hψ₁ a
    simp only [RingHom.comp_apply] at e1 ⊢
    rw [e1]
    have e2 := DFunLike.congr_fun hψ₂ ((aeval (invForms k)).toRingHom a)
    simp only [RingHom.comp_apply] at e2
    rw [e2]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
    congr 1
    rw [MvPolynomial.comp_aeval_apply (f := invForms k) (aeval (invForms k)) a]
    have : (fun l => aeval (invForms k) (invForms k l)) = X := by
      funext l; rcases l with l | l
      · have : l = 0 := Subsingleton.elim _ _
        subst this; simp [invForms]
      · simp [invForms]
    rw [this, aeval_X_left_apply]
  refine key _ _ ?_ ?_ w
  · exact IsLocalization.map_comp _
  · exact IsLocalization.map_comp _

theorem chart_inv_inv (j j' : Index) (h1 : invForms k j' = (X j : Coordinates k))
    (h2 : invForms k j = (X j' : Coordinates k)) :
    Proj.awayι (grading k) (X j) (isHomogeneous_X k j) Nat.zero_lt_one ≫ inv k ≫ inv k =
      Proj.awayι (grading k) (X j) (isHomogeneous_X k j) Nat.zero_lt_one := by
  have hQ1 : (X j : Coordinates k) = aeval (invForms k) (X j' : Coordinates k) := by
    rw [aeval_X, h1]
  have hQ2 : (X j' : Coordinates k) = aeval (invForms k) (X j : Coordinates k) := by
    rw [aeval_X, h2]
  have sq1 := Pcf.paperPForms_awayι_comp_mapTo (invForms k) 1 (invForms_homogeneous k)
    (by decide) (invForms_cover k) Nat.zero_lt_one (X j' : Coordinates k) (X j : Coordinates k)
    (isHomogeneous_X k j') hQ1
  have sq2 := Pcf.paperPForms_awayι_comp_mapTo (invForms k) 1 (invForms_homogeneous k)
    (by decide) (invForms_cover k) Nat.zero_lt_one (X j : Coordinates k) (X j' : Coordinates k)
    (isHomogeneous_X k j) hQ2
  rw [← Category.assoc]
  erw [sq1]
  rw [Category.assoc]
  erw [sq2]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, formsAwayMapTo_inv_inv k j' j
    hQ2 hQ1, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- **`z ↦ 1/z` is an involution.** -/
theorem inv_inv : inv k ≫ inv k = 𝟙 _ := by
  refine Scheme.Cover.hom_ext (MonodromyLossCurve.P1Cover k) _ _ fun j => ?_
  rw [Category.comp_id]
  rcases j with j | j
  · have : j = 0 := Subsingleton.elim _ _
    subst this
    exact chart_inv_inv k (Sum.inl 0) (Sum.inr ()) rfl rfl
  · exact chart_inv_inv k (Sum.inr ()) (Sum.inl 0) rfl rfl

#print axioms inv_inv

#print axioms zeroPt_inv
#print axioms infPt_inv

end Pcf.Examples.PaperP.MonodromyLossProductSections
