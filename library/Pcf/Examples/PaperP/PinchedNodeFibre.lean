/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.Pinched
public import Pcf.Examples.PaperP.NodalCubicLoci
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.Algebra.Polynomial.Derivative
public import Pcf.Unnormalized.Recursive
public import Pcf.Bounding.AllCodimPeriodicLift

/-!
# The restriction `g` to the nodal line `B` of the pinched plane

For `paper-p.tex`, Example `ex:pinched` ("The map `g` is neither `0`-PCF nor
`1`-PCF") and the following remark (`the fibre of g over Q is k[d]/(d²) at o`),
with `R_B = {p ∈ k[z] : p(2) = p(-2)}` and `g* p = p(z²)`:

* `NodeRing` is a domain of finite type over `k` (Artin–Tate), with `k[z]`
  finite over it.
* `pointQ a` is the image in `B` of `z = a`; `pointQ 4 = Q` is a codimension-one
  point (`divisorQ`), and `g` maps `pointQ a` to `pointQ (a²)`.
* `fibreQ_d_sq` / `fibreQ_d_ne_zero`: in the fibre ring `R_B ⧸ (g* 𝔪_Q)` the
  class of `d = z³ - 4z` is nonzero with square zero. The square is the explicit
  combination `d² = g*(z² - 16)·(8 - 5z²)/3 + g*((z² - 4)(z - 4))·8/3`; the
  nonvanishing uses the derivation `p ↦ p'(2) + p'(-2)` at the node.
* `divisorQ_mem_branchZero`: `Q ∈ branch₀(g)` for the actual affine scheme map.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedNodeFibre

open AlgebraicGeometry CategoryTheory Polynomial Pcf.Examples.Pinched

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The coordinate ring `R_B` of `B`, with a single ring structure. -/
def NodeRing : Type u := ↥(nodeAlg k)

noncomputable instance : CommRing (NodeRing k) := inferInstanceAs (CommRing ↥(nodeAlg k))
instance : IsDomain (NodeRing k) := inferInstanceAs (IsDomain ↥(nodeAlg k))
noncomputable instance : Algebra k (NodeRing k) := inferInstanceAs (Algebra k ↥(nodeAlg k))
noncomputable instance : Algebra (NodeRing k) k[X] := inferInstanceAs (Algebra ↥(nodeAlg k) k[X])
instance : IsScalarTower k (NodeRing k) k[X] :=
  inferInstanceAs (IsScalarTower k ↥(nodeAlg k) k[X])

/-- The underlying polynomial. -/
abbrev val (r : NodeRing k) : k[X] := (r : ↥(nodeAlg k)).1

omit [CharZero k] in
theorem val_mem (r : NodeRing k) : val k r ∈ nodeAlg k := (r : ↥(nodeAlg k)).2

/-- An element of `R_B`. -/
abbrev mk (p : k[X]) (hp : p ∈ nodeAlg k) : NodeRing k := (⟨p, hp⟩ : ↥(nodeAlg k))

omit [CharZero k] in
theorem algebraMap_node (r : NodeRing k) : algebraMap (NodeRing k) k[X] r = val k r := rfl

omit [CharZero k] in
theorem val_injective : Function.Injective (val k) :=
  Subtype.val_injective (p := fun p => p ∈ nodeAlg k)

omit [CharZero k] in
theorem mem_of_even (p : k[X]) : aeval (X ^ 2 : k[X]) p ∈ nodeAlg k := comp_sq_mem k p

omit [CharZero k] in
theorem mem_of_dvd (q : k[X]) : (X ^ 2 - 4) * q ∈ nodeAlg k := by
  rw [mem_nodeAlg_iff]
  simp
  norm_num

/-- The pullback `g* : p(z) ↦ p(z²)` as a ring endomorphism of `R_B`. -/
noncomputable def gStar : NodeRing k →+* NodeRing k where
  toFun r := mk k (aeval (X ^ 2 : k[X]) (val k r)) (comp_sq_mem k _)
  map_one' := by apply val_injective; simp
  map_mul' a b := by
    apply val_injective
    exact map_mul (aeval (X ^ 2 : k[X])) (val k a) (val k b)
  map_zero' := by apply val_injective; simp
  map_add' a b := by
    apply val_injective
    exact map_add (aeval (X ^ 2 : k[X])) (val k a) (val k b)

omit [CharZero k] in
theorem val_gStar (r : NodeRing k) : val k (gStar k r) = (val k r).comp (X ^ 2) := by
  change aeval (X ^ 2 : k[X]) (val k r) = _
  rw [← comp_eq_aeval]

/-- The actual affine scheme map `g : B → B`. -/
noncomputable def gScheme : Spec (.of (NodeRing k)) ⟶ Spec (.of (NodeRing k)) :=
  Spec.map (CommRingCat.ofHom (gStar k))

/-! ### Finiteness -/

omit [CharZero k] in
theorem X_sq_mem : (X ^ 2 : k[X]) ∈ nodeAlg k := by
  rw [mem_nodeAlg_iff]; simp

/-- `k[z]` is integral over `R_B`: `z` is a root of `T² - z²`. -/
instance line_isIntegral : Algebra.IsIntegral (NodeRing k) k[X] := by
  have hX : IsIntegral (NodeRing k) (X : k[X]) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (mk k (X ^ 2) (X_sq_mem k)),
      monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp [algebraMap_node]
  have hC (a : k) : IsIntegral (NodeRing k) (C a : k[X]) := by
    have := isIntegral_algebraMap (R := NodeRing k) (A := k[X])
      (x := algebraMap k (NodeRing k) a)
    rwa [← IsScalarTower.algebraMap_apply, Polynomial.algebraMap_eq] at this
  constructor
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact hp.add hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      exact (hC a).mul (hX.pow n)

instance line_finiteType : Algebra.FiniteType (NodeRing k) k[X] :=
  Algebra.FiniteType.of_restrictScalars_finiteType k (NodeRing k) k[X]

instance line_moduleFinite : Module.Finite (NodeRing k) k[X] := Algebra.IsIntegral.finite

instance line_faithfulSMul : FaithfulSMul (NodeRing k) k[X] :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (val_injective k)

/-- `R_B` is of finite type over `k` (Artin–Tate, as in the manuscript). -/
instance node_finiteType : Algebra.FiniteType k (NodeRing k) := by
  constructor
  apply fg_of_fg_of_fg (A := k) (B := NodeRing k) (C := k[X])
  · exact (Algebra.FiniteType.out : (⊤ : Subalgebra k k[X]).FG)
  · exact Module.Finite.fg_top
  · exact val_injective k

instance node_isNoetherianRing : IsNoetherianRing (NodeRing k) :=
  Algebra.FiniteType.isNoetherianRing k (NodeRing k)

/-! ### Points -/

/-- The image in `B` of the point `z = a` of the normalization. -/
noncomputable def pointQ (a : k) : Spec (.of (NodeRing k)) :=
  PrimeSpectrum.comap (algebraMap (NodeRing k) k[X]) (NodalCubic.paramPoint k a)

omit [CharZero k] in
theorem mem_pointQ_iff (a : k) (r : NodeRing k) :
    r ∈ (pointQ k a).asIdeal ↔ (val k r).eval a = 0 := Iff.rfl

instance pointQ_isMaximal (a : k) : (pointQ k a).asIdeal.IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap (NodeRing k) k[X])
    (algebraMap_isIntegral_iff.mpr inferInstance) (NodalCubic.paramPoint k a).asIdeal

theorem pointQ_height (a : k) : (pointQ k a).asIdeal.height = 1 := by
  change ((NodalCubic.paramPoint k a).asIdeal.under (NodeRing k)).height = 1
  rw [Pcf.height_under_eq_of_finite_of_finiteType k]
  exact NodalCubic.paramPoint_height k a

/-- The point `z = a` of `B` as a codimension-one point (integral effective divisor). -/
noncomputable def divisorQ (a : k) : Pcf.SchemeDivisorPoint (Spec (.of (NodeRing k))) :=
  ⟨pointQ k a, by
    rw [← idealHeight_eq_coheight (.of (NodeRing k)) (pointQ k a)]
    exact pointQ_height k a⟩

omit [CharZero k] in
/-- `g` maps the point `z = a` to `z = a²`. -/
theorem gScheme_pointQ (a : k) : gScheme k (pointQ k a) = pointQ k (a ^ 2) := by
  apply PrimeSpectrum.ext
  ext r
  change (val k (gStar k r)).eval a = 0 ↔ (val k r).eval (a ^ 2) = 0
  rw [val_gStar, eval_comp]
  simp

omit [CharZero k] in
/-- The node `o`: `z = 2` and `z = -2` give the same point. -/
theorem pointQ_neg_two : pointQ k (-2) = pointQ k 2 := by
  apply PrimeSpectrum.ext
  ext r
  change (val k r).eval (-2) = 0 ↔ (val k r).eval 2 = 0
  have h := val_mem k r
  rw [mem_nodeAlg_iff] at h
  simp only [coe_aeval_eq_eval] at h
  rw [h]

omit [CharZero k] in
/-- `g(o) = Q`: the node lies over `Q`. -/
theorem gScheme_node : gScheme k (pointQ k 2) = pointQ k 4 := by
  rw [gScheme_pointQ]; norm_num

/-- Points `z = a`, `z = b` of `B` with `a, b ∉ {±2}` agree only if `a = b`. -/
theorem pointQ_injective_off_node {a b : k} (ha : a ^ 2 ≠ 4) (h : pointQ k a = pointQ k b) :
    a = b := by
  have hmem : mk k ((X ^ 2 - 4) * (X - C a)) (mem_of_dvd k _) ∈ (pointQ k b).asIdeal := by
    rw [← h, mem_pointQ_iff]
    change ((X ^ 2 - 4) * (X - C a) : k[X]).eval a = 0
    simp
  rw [mem_pointQ_iff] at hmem
  change ((X ^ 2 - 4) * (X - C a) : k[X]).eval b = 0 at hmem
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_ofNat, mul_eq_zero,
    sub_eq_zero] at hmem
  rcases hmem with hb | hb
  · exfalso
    have hmem' : mk k ((X ^ 2 - 4) * (X - C b)) (mem_of_dvd k _) ∈
        (pointQ k a).asIdeal := by
      rw [h, mem_pointQ_iff]
      change ((X ^ 2 - 4) * (X - C b) : k[X]).eval b = 0
      simp
    rw [mem_pointQ_iff] at hmem'
    change ((X ^ 2 - 4) * (X - C b) : k[X]).eval a = 0 at hmem'
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_ofNat, mul_eq_zero,
      sub_eq_zero] at hmem'
    rcases hmem' with ha' | ha'
    · exact ha ha'
    · subst ha'
      exact ha hb
  · exact hb.symm

/-- The forward orbit `g^n(Q) = (z = 4^{2^n})` consists of distinct points. -/
theorem orbitQ_injective :
    Function.Injective fun n : ℕ => (gScheme k)^[n] (pointQ k 4) := by
  have horbit (n : ℕ) : (gScheme k)^[n] (pointQ k 4) = pointQ k ((4 : k) ^ 2 ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, gScheme_pointQ, ← pow_mul, ← pow_succ]
  intro n m h
  simp only [horbit] at h
  apply four_pow_two_pow_injective k
  apply pointQ_injective_off_node k _ h
  intro h4
  have h16 : ((4 : k) ^ 2 ^ n) ^ 2 = (2 : k) ^ 2 := by rw [h4]; norm_num
  have : ((4 ^ 2 ^ n) ^ 2 : ℕ) = (2 ^ 2 : ℕ) := by exact_mod_cast h16
  have hle : 4 ≤ 4 ^ 2 ^ n := Nat.le_self_pow (by positivity) 4
  nlinarith

/-! ### The fibre of `g` over `Q` -/

/-- The pullback of `𝔪_Q` along `g`, the ideal of the scheme fibre `g⁻¹(Q)`. -/
noncomputable def fibreIdealQ : Ideal (NodeRing k) := (pointQ k 4).asIdeal.map (gStar k)

/-- The function `d = z³ - 4z` on `B`. -/
noncomputable def dElt : NodeRing k := mk k ((X ^ 2 - 4) * X) (mem_of_dvd k _)

/-- The explicit identity `d² = g*(z² - 16)·(8 - 5z²)/3 + g*((z² - 4)(z - 4))·8/3`. -/
theorem fibreQ_d_sq : dElt k ^ 2 ∈ fibreIdealQ k := by
  have hP1 : (X ^ 2 - 16 : k[X]) ∈ nodeAlg k := by rw [mem_nodeAlg_iff]; simp
  have hA : (C (8 / 3 : k) - C (5 / 3) * X ^ 2 : k[X]) ∈ nodeAlg k := by
    rw [mem_nodeAlg_iff]; simp
  let P1 := mk k (X ^ 2 - 16) hP1
  let P2 := mk k ((X ^ 2 - 4) * (X - 4)) (mem_of_dvd k _)
  let A := mk k (C (8 / 3 : k) - C (5 / 3) * X ^ 2) hA
  have h1 : P1 ∈ (pointQ k 4).asIdeal := by
    rw [mem_pointQ_iff]
    change (X ^ 2 - 16 : k[X]).eval 4 = 0
    simp; norm_num
  have h2 : P2 ∈ (pointQ k 4).asIdeal := by
    rw [mem_pointQ_iff]
    change ((X ^ 2 - 4) * (X - 4) : k[X]).eval 4 = 0
    simp
  have hid : dElt k ^ 2 = gStar k P1 * A + gStar k P2 * algebraMap k (NodeRing k) (8 / 3) := by
    apply val_injective
    change ((X ^ 2 - 4) * X : k[X]) ^ 2 = val k (gStar k P1) * (C (8 / 3 : k) - C (5 / 3) * X ^ 2) +
      val k (gStar k P2) * C (8 / 3)
    rw [val_gStar, val_gStar]
    change _ = (X ^ 2 - 16 : k[X]).comp (X ^ 2) * _ + ((X ^ 2 - 4) * (X - 4) : k[X]).comp (X ^ 2) * _
    simp only [sub_comp, mul_comp, pow_comp, X_comp, ofNat_comp]
    have h3 : (C (8 / 3 : k)) = C 8 * C (3 : k)⁻¹ := by rw [← C_mul]; ring_nf
    have h5 : (C (5 / 3 : k)) = C 5 * C (3 : k)⁻¹ := by rw [← C_mul]; ring_nf
    have h33 : (3 : k[X]) * C (3 : k)⁻¹ = 1 := by
      rw [← map_ofNat C 3, ← C_mul, mul_inv_cancel₀ (by norm_num : (3 : k) ≠ 0), C_1]
    rw [h3, h5]
    simp only [map_ofNat]
    linear_combination (-(X ^ 2 * (X ^ 2 - 4) ^ 2) : k[X]) * h33
  rw [hid]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h1))
    (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h2))

/-- The ideal of functions vanishing at the node and killed by the
derivation `p ↦ p'(2) + p'(-2)`. -/
noncomputable def nodeTangentIdeal : Ideal (NodeRing k) where
  carrier := {r | (val k r).eval 2 = 0 ∧
    (derivative (val k r)).eval 2 + (derivative (val k r)).eval (-2) = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · change (val k a + val k b).eval 2 = 0
      simp [ha1, hb1]
    · change (derivative (val k a + val k b)).eval 2 +
        (derivative (val k a + val k b)).eval (-2) = 0
      simp only [derivative_add, eval_add]
      linear_combination ha2 + hb2
  zero_mem' := by
    show (0 : k[X]).eval 2 = 0 ∧
      (derivative (0 : k[X])).eval 2 + (derivative (0 : k[X])).eval (-2) = 0
    simp
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    have hc := val_mem k c
    have hamem := val_mem k a
    rw [mem_nodeAlg_iff] at hc hamem
    simp only [coe_aeval_eq_eval] at hc hamem
    refine ⟨?_, ?_⟩
    · change (val k c * val k a).eval 2 = 0
      simp [ha1]
    · change (derivative (val k c * val k a)).eval 2 +
        (derivative (val k c * val k a)).eval (-2) = 0
      simp only [derivative_mul, eval_add, eval_mul]
      rw [← hamem, ha1, ← hc]
      linear_combination (val k c).eval 2 * ha2

theorem fibreIdealQ_le : fibreIdealQ k ≤ nodeTangentIdeal k := by
  unfold fibreIdealQ
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [mem_pointQ_iff] at hr
  change (val k (gStar k r)).eval 2 = 0 ∧
    (derivative (val k (gStar k r))).eval 2 + (derivative (val k (gStar k r))).eval (-2) = 0
  rw [val_gStar, derivative_comp]
  have e : ((-2 : k)) ^ 2 = 4 := by norm_num
  have e2 : ((2 : k)) ^ 2 = 4 := by norm_num
  constructor
  · rw [eval_comp]
    simpa [e2] using hr
  · simp only [eval_mul, eval_comp, eval_pow, eval_X, e, e2, derivative_X_pow]
    simp

theorem dElt_not_mem_tangent : dElt k ∉ nodeTangentIdeal k := by
  intro hmem
  have h : (derivative ((X ^ 2 - 4) * X : k[X])).eval 2 +
      (derivative ((X ^ 2 - 4) * X : k[X])).eval (-2) = 0 := hmem.2
  have hd : derivative ((X ^ 2 - 4) * X : k[X]) = 3 * X ^ 2 - 4 := by
    have : ((X ^ 2 - 4) * X : k[X]) = X ^ 3 - C 4 * X := by
      rw [show (4 : k[X]) = C 4 from (map_ofNat C 4).symm]; ring
    rw [this, derivative_sub, derivative_C_mul_X, derivative_X_pow]
    rw [map_ofNat C 4]
    simp
    exact map_ofNat C 3
  rw [hd] at h
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat] at h
  norm_num at h

theorem fibreQ_d_ne : dElt k ∉ fibreIdealQ k := fun h =>
  dElt_not_mem_tangent k (fibreIdealQ_le k h)

/-- The fibre ring `R_B ⧸ g*𝔪_Q` is not reduced: `d ≠ 0` and `d² = 0` there. -/
theorem fibreQ_not_isReduced : ¬ IsReduced (NodeRing k ⧸ fibreIdealQ k) := by
  intro hred
  apply fibreQ_d_ne k
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsReduced.eq_zero
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact fibreQ_d_sq k

/-- **`Q ∈ branch₀(g)`** for the actual affine scheme map `g : B → B`. -/
theorem divisorQ_mem_branchZero :
    divisorQ k 4 ∈ Pcf.schemeUnnormalizedBranchZero (gScheme k) := by
  letI alg : Algebra (NodeRing k) (NodeRing k) := (gStar k).toAlgebra
  haveI hmax : (AffineLociBridge.divisorPrime (NodeRing k) (divisorQ k 4)).asIdeal.IsMaximal :=
    pointQ_isMaximal k 4
  have h := @AffineLociBridge.mem_branchZero_iff_quotient (NodeRing k) (NodeRing k) _ _ alg
    (divisorQ k 4) hmax
  change divisorQ k 4 ∈ Pcf.schemeUnnormalizedBranchZero
    (Spec.map (CommRingCat.ofHom (@algebraMap (NodeRing k) (NodeRing k) _ _ alg)))
  rw [h]
  exact fibreQ_not_isReduced k

#print axioms node_finiteType
#print axioms divisorQ
#print axioms gScheme_pointQ
#print axioms gScheme_node
#print axioms orbitQ_injective
#print axioms fibreQ_d_sq
#print axioms fibreQ_d_ne
#print axioms fibreQ_not_isReduced
#print axioms divisorQ_mem_branchZero

/-! ### `g` is finite and surjective; `Q ∈ branch₁(g)`; `PC₀(g)`, `PC₁(g)` infinite -/

omit [CharZero k] in
theorem gStar_comp_algebraMap :
    (gStar k).comp (algebraMap k (NodeRing k)) = algebraMap k (NodeRing k) := by
  ext c
  apply val_injective
  change aeval (X ^ 2 : k[X]) (C c) = C c
  simp

omit [CharZero k] in
theorem gStar_injective : Function.Injective (gStar k) := by
  intro a b h
  apply val_injective
  have h' := congrArg (val k) h
  rw [val_gStar, val_gStar] at h'
  have e (p : k[X]) : p.comp (X ^ 2) = expand k 2 p := by
    rw [expand_eq_comp_X_pow]
  rw [e, e] at h'
  exact expand_injective (by norm_num) h'

/-- `k[z]` is integral over `R_B` through `g*`: `z` is a root of `T⁴ - g*(z²)`. -/
theorem line_isIntegralElem_over_g (p : k[X]) :
    ((algebraMap (NodeRing k) k[X]).comp (gStar k)).IsIntegralElem p := by
  let φ := (algebraMap (NodeRing k) k[X]).comp (gStar k)
  have hX : φ.IsIntegralElem (X : k[X]) := by
    refine ⟨Polynomial.X ^ 4 - Polynomial.C (mk k (X ^ 2) (X_sq_mem k)),
      monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
    change (X : k[X]) ^ 4 - val k (gStar k (mk k (X ^ 2) (X_sq_mem k))) = 0
    rw [val_gStar]
    change (X : k[X]) ^ 4 - (X ^ 2 : k[X]).comp (X ^ 2) = 0
    simp only [pow_comp, X_comp]
    ring
  have hC (a : k) : φ.IsIntegralElem (C a) := by
    have h := RingHom.isIntegralElem_map φ (x := algebraMap k (NodeRing k) a)
    have hφ : φ (algebraMap k (NodeRing k) a) = C a := by
      change val k (gStar k (algebraMap k (NodeRing k) a)) = C a
      rw [← RingHom.comp_apply, gStar_comp_algebraMap]
      rfl
    rwa [hφ] at h
  have hpow (n : ℕ) : φ.IsIntegralElem ((X : k[X]) ^ n) := by
    induction n with
    | zero => simpa using RingHom.isIntegralElem_map φ (x := 1)
    | succ n ih => rw [pow_succ]; exact RingHom.IsIntegralElem.mul φ ih hX
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact RingHom.IsIntegralElem.add φ hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      exact RingHom.IsIntegralElem.mul φ (hC a) (hpow n)

/-- `g* : R_B → R_B` is finite. -/
theorem gStar_finite : (gStar k).Finite := by
  refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
  · intro r
    obtain ⟨P, hP, hev⟩ := line_isIntegralElem_over_g k (val k r)
    refine ⟨P, hP, ?_⟩
    apply val_injective
    change algebraMap (NodeRing k) k[X] (P.eval₂ (gStar k) r) = algebraMap (NodeRing k) k[X] 0
    rw [Polynomial.hom_eval₂, map_zero]
    exact hev
  · apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (NodeRing k))
    rw [gStar_comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

instance gScheme_isFinite : IsFinite (gScheme k) :=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom (gStar k))).mpr (gStar_finite k)

instance gScheme_surjective : Surjective (gScheme k) := by
  constructor
  exact (gStar_finite k).to_isIntegral.comap_surjective (gStar_injective k)

instance gScheme_isDominant : IsDominant (gScheme k) := inferInstance

instance pointQ_residueField_charZero (a : k) :
    CharZero (pointQ k a).asIdeal.ResidueField :=
  charZero_of_injective_ringHom
    (f := (algebraMap (NodeRing k) (pointQ k a).asIdeal.ResidueField).comp
      (algebraMap k (NodeRing k)))
    (RingHom.injective _)

/-- **`Q ∈ branch₁(g)`**. -/
theorem divisorQ_mem_branchOne :
    divisorQ k 4 ∈ Pcf.schemeUnnormalizedBranchOne (gScheme k) := by
  letI alg : Algebra (NodeRing k) (NodeRing k) := (gStar k).toAlgebra
  haveI hfin : @Module.Finite (NodeRing k) (NodeRing k) _ _ alg.toModule := gStar_finite k
  haveI : CharZero (AffineLociBridge.divisorPrime (NodeRing k) (divisorQ k 4)).asIdeal.ResidueField :=
    pointQ_residueField_charZero k 4
  exact @AffineLociBridge.mem_branchOne_of_mem_branchZero (NodeRing k) (NodeRing k) _ _ alg
    hfin (divisorQ k 4) _ (divisorQ_mem_branchZero k)

/-- The structure morphism `B → Spec k`. -/
noncomputable def structureMap : Spec (.of (NodeRing k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (NodeRing k)))

instance structureMap_locallyOfFiniteType : LocallyOfFiniteType (structureMap k) := by
  unfold structureMap
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **`g` is neither `0`-PCF nor `1`-PCF**: the actual unnormalized
postcritical sets of `g : B → B` (Definition `def:pcf-unnormalized`) are
infinite, since they contain the distinct points `g^n(Q) = (z = 4^{2^n})`.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem not_isSchemeUnnormalizedPCF (i : Bool) :
    ¬ Pcf.IsSchemeUnnormalizedPCF i k (structureMap k) (gScheme k) := by
  intro hfin
  have hmem : divisorQ k 4 ∈ Pcf.schemeUnnormalizedBranch i (gScheme k) := by
    cases i
    · exact divisorQ_mem_branchZero k
    · exact divisorQ_mem_branchOne k
  let F : ℕ → Pcf.SchemeDivisorPoint (Spec (.of (NodeRing k))) := fun n =>
    Pcf.schemeDivisorIterateOfFiniteType k (structureMap k) (gScheme k) n (divisorQ k 4)
  have hF : Function.Injective F := by
    intro n m h
    have h' := congrArg Subtype.val h
    simp only [F, Pcf.schemeDivisorIterateOfFiniteType_val] at h'
    change Pcf.schemePointIterate (gScheme k) n (pointQ k 4) =
      Pcf.schemePointIterate (gScheme k) m (pointQ k 4) at h'
    rw [Pcf.schemePointIterate_eq_function_iterate,
      Pcf.schemePointIterate_eq_function_iterate] at h'
    exact orbitQ_injective k h'
  apply Set.infinite_of_injective_forall_mem hF (s := Pcf.schemeUnnormalizedPostcriticalSet i k
    (structureMap k) (gScheme k)) _ hfin
  intro n
  exact Set.mem_iUnion.mpr ⟨n, divisorQ k 4, hmem, rfl⟩

#print axioms gStar_finite
#print axioms divisorQ_mem_branchOne
#print axioms not_isSchemeUnnormalizedPCF

/-- `Q ≠ o`: `Q` is not the glued point. -/
theorem pointQ_four_ne_node : pointQ k 4 ≠ pointQ k 2 := by
  intro h
  have := pointQ_injective_off_node k (by norm_num) h
  norm_num at this

/-- `B` is the nodal cubic `d² = b(b - 4)²` in `b = z²`, `d = z³ - 4z`. -/
theorem nodal_cubic_relation :
    dElt k ^ 2 = mk k (X ^ 2) (X_sq_mem k) * (mk k (X ^ 2) (X_sq_mem k) - 4) ^ 2 := by
  apply val_injective
  change ((X ^ 2 - 4) * X : k[X]) ^ 2 = X ^ 2 * (X ^ 2 - 4) ^ 2
  ring

#print axioms pointQ_four_ne_node
#print axioms nodal_cubic_relation

end Pcf.Examples.PaperP.PinchedNodeFibre
