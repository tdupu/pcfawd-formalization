/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiEtale
public import Pcf.Examples.PaperP.MonodromyLossYMap
public import Pcf.Examples.PaperP.MonodromyLossReturnScheme

/-!
# The return identity `y ∘ φ² = g ∘ y` as scheme morphisms (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss`: "`φ² = 2ι` and the duplication formula gives
`y(2P) = -(y(P)⁴ + 1)/y(P)³`", so that `y(φ² P) = g(y(P))` with `g(y) = -i (y⁴ + 1)/y³`.

Here this is proved as an equality of morphisms of schemes `E ⟶ ℙ¹`:

* **`yMap_comp_schemeMap : yMap ≫ g = φ ≫ φ ≫ yMap`**.

`E` is reduced and `ℙ¹ = Proj k[u, v]` is separated, so it suffices to compare the two maps
after the dominant map `Spec (Frac A) ⟶ Spec A ⟶ E` (`ext_of_isDominant`). There both sides are
`Frac A`-points of `ℙ¹` in the chart `D₊(v)`:

* `phi_point`: a `T`-point `a` of the finite chart with `a(x)` invertible is sent by `φ` to the
  `T`-point `(i(x² - 1)/x, -(1 + i) y (x² + 1)/x²)` of the finite chart;
* `yMap_point`: a `T`-point `a` of the finite chart goes to `[a(y) : 1]`;
* `schemeMap_point'`: `g [z : 1] = [-i(z⁴ + 1)/z³ : 1]` for `z` invertible
  (through `awayEval_formsAwayMap`, the chart description of `g`);
* `return_field_identity`: the rational identity in a field of characteristic `3`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossCurve

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open BasilicaProjectiveScheme (Index Coordinates grading)

/-- The rational identity behind the return: with `X₁ = c(X² - 1)/X`,
`Y₁ = -(1 + c) Y (X² + 1)/X²` and `Y₂ = -(1 + c) Y₁ (X₁² + 1)/X₁²` (the `y`-coordinate of
`φ²(X, Y)`), one has `Y₂ = -c (Y⁴ + 1)/Y³`. -/
theorem return_field_identity {F : Type*} [Field F] (X Y c : F) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hX1 : X ^ 2 - 1 ≠ 0) (hc0 : c ≠ 0) (h : Y ^ 2 = X ^ 3 - X) (hc : c ^ 2 = -1)
    (h3 : (3 : F) = 0) :
    -(1 + c) * (-(1 + c) * Y * (X ^ 2 + 1) * X⁻¹ ^ 2) *
        ((c * (X ^ 2 - 1) * X⁻¹) ^ 2 + 1) * (c * (X ^ 2 - 1) * X⁻¹)⁻¹ ^ 2 =
      -c * (Y ^ 4 + 1) / Y ^ 3 := by
  field_simp
  linear_combination (-X^3*Y^4*c^4 - X^3*Y^4*c^2 - X^3*c^3 + X*Y^4*c^3 - X*Y^4*c^2 + X*Y^4*c -
      X*Y^4 + X*c^3 - Y^6*c^4 - Y^6*c^2 - Y^2*c^3) * h +
    (-X^2*Y^4*c^2 + X^2*Y^4*c - X^2*Y^4 + X*Y^6*c^2 - X*Y^6*c + X*Y^6 + Y^8*c^2 + Y^4*c^2) * hc +
    (X^6*Y^4*c^3 - X^4*Y^4*c^3 + X^4*Y^4*c - X^2*Y^4*c^3 + X^2*Y^4*c^2 + X^2*Y^4 + Y^4*c^3) * h3

section AwayEvalForms

variable {k : Type u} [Field k] {T : Type u} [CommRing T] [Algebra k T]

/-- Evaluating after the chart pullback of a forms-defined map `[F]` is evaluating at `F(x)`. -/
theorem awayEval_formsAwayMap (F : Index → Coordinates k) (d : ℕ)
    (hF : ∀ j, (F j).IsHomogeneous d) (P : Coordinates k) (x : Index → T)
    (h : IsUnit (aeval x (aeval F P))) (h' : IsUnit (aeval (fun j => aeval x (F j)) P)) :
    (awayEval (aeval F P) x h).comp (Pcf.paperPFormsAwayMap F d hF P) =
      awayEval P (fun j => aeval x (F j)) h' := by
  ext z
  simp only [awayEval, RingHom.comp_apply]
  change IsLocalization.Away.lift (aeval F P) h (Pcf.paperPFormsAwayMap F d hF P z).val =
    IsLocalization.Away.lift P h' z.val
  rw [Pcf.paperPFormsAwayMap, Pcf.paperPDegreeLocalizationMap_val]
  generalize z.val = w
  have key : ∀ hPQ, (IsLocalization.Away.lift (aeval F P) (S := Localization.Away (aeval F P))
      h).comp (IsLocalization.map (M := Submonoid.powers P) (S := Localization.Away P)
        (T := Submonoid.powers (aeval F P)) (Localization.Away (aeval F P)) (aeval F).toRingHom
        hPQ) =
      IsLocalization.Away.lift P (S := Localization.Away P) h' := by
    intro hPQ
    refine IsLocalization.ringHom_ext (Submonoid.powers P) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, IsLocalization.map_eq, IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact MvPolynomial.comp_aeval_apply (f := F) (aeval x) a
  exact DFunLike.congr_fun (key _) w

theorem awayEval_congr {f : Coordinates k} {x x' : Index → T} (hx : x = x')
    (h : IsUnit (aeval x f)) (h' : IsUnit (aeval x' f)) : awayEval f x h = awayEval f x' h' := by
  subst hx; rfl

end AwayEvalForms

section Points

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

local notation "uu" => (X (Sum.inl 0) : Coordinates k)
local notation "vv" => (X (Sum.inr ()) : Coordinates k)
local notation "P1" => Proj (grading k)

variable {K : Type u} [Field K] [Algebra k K]

/-- The homogeneous coordinates `[z : 1]`. -/
noncomputable def pt (z : K) : Index → K := Sum.elim (fun _ => z) (fun _ => 1)

omit [CharP k 3] in
theorem pt_v (z : K) : IsUnit (aeval (pt z) vv) := by simp [pt]

omit [CharP k 3] in
theorem vv_mem : vv ∈ grading k 1 := isHomogeneous_X k _

/-- The chart point `[z : 1] : Spec K ⟶ D₊(v) ⊆ ℙ¹`. -/
noncomputable def ptMap (z : K) : Spec (.of K) ⟶ P1 :=
  Spec.map (CommRingCat.ofHom (awayEval vv (pt z) (pt_v k z))) ≫
    Proj.awayι (grading k) vv (vv_mem k) Nat.zero_lt_one

include hi in
/-- **`φ` on a `K`-point of the finite chart with `x ≠ 0`.** -/
theorem phi_point (a : A k →+* K) (ha : ∀ r : k, a (algebraMap k (A k) r) = algebraMap k K r)
    (hX : a (xA k) ≠ 0) :
    ∃ b : A k →+* K, (∀ r : k, b (algebraMap k (A k) r) = algebraMap k K r) ∧
      b (xA k) = algebraMap k K i * (a (xA k) ^ 2 - 1) * (a (xA k))⁻¹ ∧
      b (yA k) = -(1 + algebraMap k K i) * a (yA k) * (a (xA k) ^ 2 + 1) * (a (xA k))⁻¹ ^ 2 ∧
      Spec.map (CommRingCat.ofHom a) ≫ ιA k ≫ phi k i hi =
        Spec.map (CommRingCat.ofHom b) ≫ ιA k := by
  let ψ : Ax k →+* K := IsLocalization.Away.lift (xA k) (IsUnit.mk0 _ hX)
  have hψ : ψ.comp (algebraMap (A k) (Ax k)) = a := IsLocalization.Away.lift_comp _ _
  have hψa (r : A k) : ψ (algebraMap (A k) (Ax k) r) = a r := DFunLike.congr_fun hψ r
  have hinv : ψ (invX k) = (a (xA k))⁻¹ := by
    have := congrArg ψ (IsLocalization.Away.mul_invSelf (S := Ax k) (xA k))
    rw [map_mul, map_one, hψa] at this
    exact eq_inv_of_mul_eq_one_right this
  have hψc (r : k) : ψ (algebraMap k (Ax k) r) = algebraMap k K r := by
    rw [IsScalarTower.algebraMap_apply k (A k) (Ax k), hψa, ha]
  refine ⟨ψ.comp (phi1 k i hi), fun r => ?_, ?_, ?_, ?_⟩
  · rw [RingHom.comp_apply, phi1_algebraMap, hψc]
  · simp only [RingHom.comp_apply, phi1, liftA_x, map_mul, map_sub, map_pow, map_one, hψa,
      hinv, hψc]
  · simp only [RingHom.comp_apply, phi1, liftA_y, map_mul, map_neg, map_add, map_pow, map_one,
      hψa, hinv, hψc]
  · rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, phi_D_x, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]

omit [CharP k 3] in
/-- **`y` on a `K`-point of the finite chart**: `P ↦ [y(P) : 1]`. -/
theorem yMap_point (a : A k →+* K) (ha : ∀ r : k, a (algebraMap k (A k) r) = algebraMap k K r) :
    Spec.map (CommRingCat.ofHom a) ≫ ιA k ≫ yMap k = ptMap k (a (yA k)) := by
  let aₐ : A k →ₐ[k] K := { a with commutes' := ha }
  have hB : IsUnit (aeval (fun j => aₐ (valsA k j)) vv) := by simp [valsA]
  have e := awayEval_comp aₐ vv (valsA k) (valsA_v k) hB
  rw [ιA_yMap, yChartA, ptMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine e.trans (awayEval_congr ?_ _ _)
  funext j
  rcases j with _ | _ <;> simp [valsA, pt, aₐ]

omit [CharP k 3] in
include hi in
/-- **The return `g` on a chart point**: `g [z : 1] = [w : 1]` where `w z³ = -i (z⁴ + 1)`. -/
theorem ptMap_schemeMap (z w : K) (hz : z ≠ 0)
    (hw : z ^ 3 * w = -algebraMap k K i * (z ^ 4 + 1)) :
    ptMap k z ≫ MonodromyLossReturn.schemeMap k i hi = ptMap k w := by
  have hxP : aeval (MonodromyLossReturn.forms k i) vv = vv * uu ^ 3 := by
    rw [aeval_X, MonodromyLossReturn.forms_inr, mul_comm]
  have hu3 : uu ^ 3 ∈ grading k 3 := by
    simpa using (isHomogeneous_X k (Sum.inl 0 : Index)).pow 3
  have hzx : IsUnit (aeval (pt z) (aeval (MonodromyLossReturn.forms k i) vv)) := by
    rw [hxP]; simpa [pt] using hz
  have e2 := awayEval_awayMap hu3 hxP (pt z) hzx (pt_v k z)
  have e3 := awayEval_formsAwayMap (MonodromyLossReturn.forms k i) 4
    (MonodromyLossReturn.forms_homogeneous k i) vv (pt z) hzx
    (by simpa [pt, MonodromyLossReturn.forms] using hz)
  have e4 := Pcf.paperPForms_awayι_comp_map (MonodromyLossReturn.forms k i) 4 (by decide)
    (MonodromyLossReturn.forms_homogeneous k i) (MonodromyLossReturn.forms_cover k hi)
    Nat.zero_lt_one vv (isHomogeneous_X k _)
  have hsc : (fun j => aeval (pt z) (MonodromyLossReturn.forms k i j)) =
      fun j => z ^ 3 * pt w j := by
    funext j
    rcases j with _ | _
    · simp only [MonodromyLossReturn.forms, pt, Sum.elim_inl, map_mul, aeval_C, map_add,
        map_pow, aeval_X, Sum.elim_inr, one_pow, map_neg]
      rw [hw]
    · simp [MonodromyLossReturn.forms, pt]
  have e5 := awayEval_smul (k := k) (isHomogeneous_X k (Sum.inr () : Index)) (z ^ 3) (pt w)
    (by rw [← hsc]; simpa [pt, MonodromyLossReturn.forms] using hz) (pt_v k w)
  have e6 : Spec.map (CommRingCat.ofHom (awayMap (grading k) hu3 hxP)) ≫
      Proj.awayι (grading k) vv (vv_mem k) Nat.zero_lt_one ≫
        MonodromyLossReturn.schemeMap k i hi =
      Spec.map (CommRingCat.ofHom (Pcf.paperPFormsAwayMap (MonodromyLossReturn.forms k i) 4
        (MonodromyLossReturn.forms_homogeneous k i) vv)) ≫
        Proj.awayι (grading k) vv (vv_mem k) Nat.zero_lt_one := by
    rw [Proj.SpecMap_awayMap_awayι_assoc]
    exact e4
  rw [ptMap, ptMap, ← e2, CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [e6]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e3, ← e5]
  congr 3
  exact awayEval_congr hsc _ _

include hi in
/-- **The return identity** of `ex:monodromy-loss` as an equality of scheme morphisms
`E ⟶ ℙ¹`: `y ∘ φ² = g ∘ y`, with `g(y) = -i (y⁴ + 1)/y³`.

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem yMap_comp_schemeMap :
    yMap k ≫ MonodromyLossReturn.schemeMap k i hi = phi k i hi ≫ phi k i hi ≫ yMap k := by
  refine ext_of_isDominant
    (Spec.map (CommRingCat.ofHom (algebraMap (A k) (FractionRing (A k)))) ≫ ιA k) ?_
  set K := FractionRing (A k)
  set a0 := algebraMap (A k) K
  have hinj : Function.Injective a0 := IsFractionRing.injective _ _
  set X' := a0 (xA k)
  set Y' := a0 (yA k)
  set c := algebraMap k K i
  have hX : X' ≠ 0 := fun h => xA_ne_zero k (hinj (h.trans (map_zero _).symm))
  have hY : Y' ≠ 0 := fun h => yA_ne_zero k (hinj (h.trans (map_zero _).symm))
  have hX1 : X' ^ 2 - 1 ≠ 0 := by
    intro h
    apply qA_ne_zero k
    apply hinj
    simp only [qA, map_sub, map_pow, map_one, map_zero]
    linear_combination (X' ^ 2 + 1) * h
  have hc : c ^ 2 = -1 := by
    have := congrArg (algebraMap k K) hi; simpa using this
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hrel : Y' ^ 2 = X' ^ 3 - X' := by
    have := congrArg a0 (A_rel k); simpa using this
  have h3 := three_eq_zero k K
  have ha0 (r : k) : a0 (algebraMap k (A k) r) = algebraMap k K r :=
    (IsScalarTower.algebraMap_apply k (A k) K r).symm
  obtain ⟨b1, hb1c, hb1x, hb1y, e1⟩ := phi_point k i hi a0 ha0 hX
  obtain ⟨b2, hb2c, -, hb2y, e2⟩ := phi_point k i hi b1 hb1c (by
    rw [hb1x]
    exact mul_ne_zero (mul_ne_zero hc0 hX1) (inv_ne_zero hX))
  have lhs : (Spec.map (CommRingCat.ofHom a0) ≫ ιA k) ≫ yMap k ≫
      MonodromyLossReturn.schemeMap k i hi = ptMap k (-c * (Y' ^ 4 + 1) / Y' ^ 3) := by
    rw [Category.assoc, ← Category.assoc (ιA k), ← Category.assoc, yMap_point k a0 ha0]
    refine ptMap_schemeMap k i hi Y' _ hY ?_
    rw [mul_comm]
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hY)
  have rhs : (Spec.map (CommRingCat.ofHom a0) ≫ ιA k) ≫ phi k i hi ≫ phi k i hi ≫ yMap k =
      ptMap k (b2 (yA k)) := by
    rw [Category.assoc, ← Category.assoc (ιA k), ← Category.assoc, e1, Category.assoc,
      ← Category.assoc (ιA k), ← Category.assoc, e2, Category.assoc, yMap_point k b2 hb2c]
  rw [lhs, rhs, hb2y, hb1y, hb1x]
  congr 1
  exact (return_field_identity X' Y' c hX hY hX1 hc0 hrel hc h3).symm

end Points

#print axioms awayEval_formsAwayMap
#print axioms phi_point
#print axioms yMap_point
#print axioms ptMap_schemeMap
#print axioms yMap_comp_schemeMap

end Pcf.Examples.PaperP.MonodromyLossCurve
