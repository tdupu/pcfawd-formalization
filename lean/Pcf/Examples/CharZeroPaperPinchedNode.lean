/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperPinchedBranch
public import Pcf.Examples.CharZeroPaperPinchedCone

/-!
# The nodal curve `B` of `paper.tex`, Example `ex:pinched`

The coordinate ring of `B` is the displayed presentation
`k[B] = k[b,d]/(d² - b(b-4)²)` (`NodalRing`). This file proves:

* `nodalParam : k[B] → k[z]`, `b ↦ z²`, `d ↦ z(z²-4)`, is injective with image
  `{p : p(2) = p(-2)}` (`nodalParam_injective`, `mem_range_nodalParam_iff`);
  hence `k[B]` is a domain, `k[z]` is its integral closure, and
  `lineNormalizationIso` identifies `𝔸¹` with the canonical normalization of `B`;
* `gStar : b ↦ b²`, `d ↦ b³ - 4b` is the displayed action; it lifts to `z ↦ z²`
  on `𝔸¹` and the actual map `g : B → B` is finite and surjective;
* the canonical normalized lift of `g` is `z ↦ z²` (`line_lift_eq`), whose only
  branch divisor is `z = 0`; hence `g` is normalized-PCF (`line_isNormalizedPCF`);
* the actual scheme fibre of `g` over `Q = (b,d) = (16,48)` is
  `Spec k[d]/(d²)` (`fiberQ_iso`), supported at the node `(4,0)`
  (`gScheme_eq_Q_iff`); so `Q` lies in the nonreduced-fibre branch locus and `g`
  is not formally étale at the node;
* the forward orbit of `Q` consists of the distinct points `z = 4^{2^n}`.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperPinched

open CategoryTheory AlgebraicGeometry Pcf.PaperCharZero Polynomial
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

variable (k : Type u) [Field k]

/-! ### The presentation `k[b,d]/(d² - b(b-4)²)` -/

/-- The nodal relation `d² - b(b-4)²` (variable `0` is `b`, `1` is `d`). -/
def nodalRelation : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 * (MvPolynomial.X 0 - 4) ^ 2

/-- The displayed coordinate ring `k[B] = k[b,d]/(d² - b(b-4)²)`. -/
abbrev NodalRing := MvPolynomial (Fin 2) k ⧸ Ideal.span {nodalRelation k}

/-- The class of `b`. -/
abbrev bB : NodalRing k := Ideal.Quotient.mk _ (MvPolynomial.X 0)
/-- The class of `d`. -/
abbrev dB : NodalRing k := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The normalization parameter `b ↦ z²`, `d ↦ z(z² - 4)`. -/
def nodalParam : NodalRing k →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![X ^ 2, X * (X ^ 2 - 4)]) <| by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have : MvPolynomial.aeval ![(X : Polynomial k) ^ 2, X * (X ^ 2 - 4)] (nodalRelation k) = 0 := by
      simp [nodalRelation]; ring
    rw [map_mul, this, mul_zero]

theorem nodalParam_mk (F : MvPolynomial (Fin 2) k) :
    nodalParam k (Ideal.Quotient.mk _ F) = MvPolynomial.aeval ![X ^ 2, X * (X ^ 2 - 4)] F := rfl

@[simp] theorem nodalParam_b : nodalParam k (bB k) = X ^ 2 := by
  rw [nodalParam_mk]; simp

@[simp] theorem nodalParam_d : nodalParam k (dB k) = X * (X ^ 2 - 4) := by
  rw [nodalParam_mk]; simp

/-- Every polynomial is congruent to `e(b) + d·v(b)` modulo the nodal relation. -/
theorem exists_reduce_nodal (F : MvPolynomial (Fin 2) k) :
    ∃ e v : Polynomial k, F - (aeval (MvPolynomial.X 0) e +
      MvPolynomial.X 1 * aeval (MvPolynomial.X 0) v) ∈ Ideal.span {nodalRelation k} := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, hp⟩ := hp
    obtain ⟨c, d, hq⟩ := hq
    refine ⟨a + c, b + d, ?_⟩
    convert Ideal.add_mem _ hp hq using 1
    simp only [map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨e, v, hp⟩ := hp
    have h1 := Ideal.mul_mem_right (MvPolynomial.X i) _ hp
    fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h1 ⊢
    · refine ⟨e * X, v * X, ?_⟩
      convert h1 using 1
      simp only [map_mul, aeval_X]
      ring
    · refine ⟨v * (X * (X - 4) ^ 2), e, ?_⟩
      have h2 : aeval (MvPolynomial.X 0) v * nodalRelation k ∈
          Ideal.span {nodalRelation k} := Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      convert Ideal.add_mem _ h1 h2 using 1
      simp only [map_mul, map_pow, map_sub, aeval_X, map_ofNat, nodalRelation]
      ring

theorem nodalParam_aeval (e : Polynomial k) :
    MvPolynomial.aeval ![X ^ 2, X * (X ^ 2 - 4)] (aeval (MvPolynomial.X 0 :
      MvPolynomial (Fin 2) k) e) = e.comp (X ^ 2) := by
  rw [← Polynomial.aeval_algHom_apply, comp_eq_aeval]
  simp

variable [CharZero k]

theorem nodalParam_injective : Function.Injective (nodalParam k) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨e, v, hev⟩ := exists_reduce_nodal k F
  have hF : Ideal.Quotient.mk (Ideal.span {nodalRelation k}) F =
      Ideal.Quotient.mk _ (aeval (MvPolynomial.X 0) e +
        MvPolynomial.X 1 * aeval (MvPolynomial.X 0) v) :=
    Ideal.Quotient.eq.mpr hev
  rw [hF] at hr ⊢
  rw [nodalParam_mk] at hr
  simp only [map_add, map_mul, nodalParam_aeval, MvPolynomial.aeval_X, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hr
  have hr' : e.comp (X ^ 2) + X * (X ^ 2 - 4) * v.comp (X ^ 2) = 0 := by
    linear_combination hr
  have hσ0 := congrArg (fun p : Polynomial k => p.comp (-X)) hr'
  simp only [add_comp, mul_comp, sub_comp, pow_comp, X_comp, comp_assoc, neg_sq,
    zero_comp, ofNat_comp] at hσ0
  have hσ : e.comp (X ^ 2) - X * (X ^ 2 - 4) * v.comp (X ^ 2) = 0 := by
    linear_combination hσ0
  have h2E : (2 : Polynomial k) * e.comp (X ^ 2) = 0 := by linear_combination hr' + hσ
  have hE0 : e.comp (X ^ 2) = 0 := by
    rcases mul_eq_zero.mp h2E with h | h
    · exact absurd h (by
        rw [show (2 : Polynomial k) = C 2 from (map_ofNat C 2).symm]
        exact C_ne_zero.mpr two_ne_zero)
    · exact h
  have hO0 : X * (X ^ 2 - 4) * v.comp (X ^ 2) = 0 := by rw [← hr', hE0, zero_add]
  have hne : (X * (X ^ 2 - 4) : Polynomial k) ≠ 0 := by
    intro h
    have := congrArg (eval 1) h
    norm_num at this
  have hv : v.comp (X ^ 2) = 0 := (mul_eq_zero.mp hO0).resolve_left hne
  have he : e = 0 := by
    apply expand_injective (n := 2) (by norm_num)
    rw [map_zero, expand_eq_comp_X_pow]
    exact hE0
  have hv' : v = 0 := by
    apply expand_injective (n := 2) (by norm_num)
    rw [map_zero, expand_eq_comp_X_pow]
    exact hv
  simp [he, hv']

instance nodalRing_isDomain : IsDomain (NodalRing k) :=
  (nodalParam_injective k).isDomain (nodalParam k).toRingHom

/-- Evaluating the image at `a` is evaluating at `(a², a(a²-4))`. -/
theorem eval_nodalParam_mk (a : k) (F : MvPolynomial (Fin 2) k) :
    (nodalParam k (Ideal.Quotient.mk _ F)).eval a =
      MvPolynomial.eval ![a ^ 2, a * (a ^ 2 - 4)] F := by
  rw [nodalParam_mk]
  change (Polynomial.aeval a) (MvPolynomial.aeval _ F) = MvPolynomial.aeval _ F
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  fin_cases i <;> simp

theorem nodalParam_eval_two (r : NodalRing k) :
    (nodalParam k r).eval 2 = (nodalParam k r).eval (-2) := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [eval_nodalParam_mk, eval_nodalParam_mk]
  congr 2
  funext i
  fin_cases i <;> norm_num

theorem mem_range_of (r : NodalRing k) {p : Polynomial k} (h : nodalParam k r = p) :
    p ∈ (nodalParam k).range := ⟨r, h⟩

/-- `(z² - 4)·zⁿ` lies in the image of the parameter. -/
theorem sq_sub_four_mul_mem_range (q : Polynomial k) :
    (X ^ 2 - 4) * q ∈ (nodalParam k).range := by
  have hpow : ∀ n : ℕ, (X ^ 2 - 4) * X ^ n ∈ (nodalParam k).range := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => exact mem_range_of k (bB k - 4) (by rw [map_sub, nodalParam_b, map_ofNat]; ring)
      | 1, _ => exact mem_range_of k (dB k) (by rw [nodalParam_d]; ring)
      | n + 2, ih =>
        obtain ⟨r, hr⟩ := ih n (by omega)
        change nodalParam k r = _ at hr
        exact mem_range_of k (bB k * r) (by rw [map_mul, hr, nodalParam_b]; ring)
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add]; exact add_mem hp hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_left_comm]
    obtain ⟨r, hr⟩ := hpow n
    change nodalParam k r = _ at hr
    exact mem_range_of k (algebraMap k _ a * r) (by rw [map_mul, hr, AlgHom.commutes]; rfl)

/-- **The image of `k[B]` in `k[z]` is `{p : p(2) = p(-2)}`.** -/
theorem mem_range_nodalParam_iff (p : Polynomial k) :
    p ∈ (nodalParam k).range ↔ p.eval 2 = p.eval (-2) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact nodalParam_eval_two k r
  · intro hp
    set c := p.eval 2
    have h2 : (p - C c).IsRoot 2 := by simp [c]
    obtain ⟨q1, hq1⟩ := dvd_iff_isRoot.mpr h2
    have hm2 : (p - C c).IsRoot (-2) := by simp [c, hp]
    have hq1m : q1.IsRoot (-2) := by
      rw [hq1, IsRoot, eval_mul] at hm2
      simp only [eval_sub, eval_X, eval_C] at hm2
      rcases mul_eq_zero.mp hm2 with h | h
      · norm_num at h
      · exact h
    obtain ⟨q2, hq2⟩ := dvd_iff_isRoot.mpr hq1m
    have hpq : p = C c + (X - C 2) * ((X - C (-2)) * q2) := by
      rw [← hq2, ← hq1]; ring
    have : p = C c + (X ^ 2 - 4) * q2 := by
      rw [hpq]; simp only [map_neg, map_ofNat]; ring
    rw [this]
    exact add_mem (mem_range_of k (algebraMap k _ c) (by rw [AlgHom.commutes]; rfl))
      (sq_sub_four_mul_mem_range k q2)

/-! ### Normalization of `B` -/

instance : Algebra (NodalRing k) (Polynomial k) := (nodalParam k).toRingHom.toAlgebra

theorem algebraMap_nodal (r : NodalRing k) :
    algebraMap (NodalRing k) (Polynomial k) r = nodalParam k r := rfl

instance : IsScalarTower k (NodalRing k) (Polynomial k) :=
  IsScalarTower.of_algebraMap_eq fun a => ((nodalParam k).commutes a).symm

instance nodal_faithfulSMul : FaithfulSMul (NodalRing k) (Polynomial k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (nodalParam_injective k)

instance line_isIntegral_nodal : Algebra.IsIntegral (NodalRing k) (Polynomial k) := by
  have hX : IsIntegral (NodalRing k) (X : Polynomial k) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (bB k), monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp [algebraMap_nodal]
  have hC (a : k) : IsIntegral (NodalRing k) (C a : Polynomial k) := by
    have := isIntegral_algebraMap (R := NodalRing k) (A := Polynomial k)
      (x := algebraMap k (NodalRing k) a)
    rwa [← IsScalarTower.algebraMap_apply, Polynomial.algebraMap_eq] at this
  constructor
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact hp.add hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      exact (hC a).mul (hX.pow n)

instance line_moduleFinite_nodal : Module.Finite (NodalRing k) (Polynomial k) := by
  haveI : Algebra.FiniteType (NodalRing k) (Polynomial k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (NodalRing k) (Polynomial k)
  exact Algebra.IsIntegral.finite

instance nodal_isFractionRing : IsFractionRing (NodalRing k) (FractionRing (Polynomial k)) := by
  refine isFractionRing_of_conductor (A := NodalRing k) (B := Polynomial k) (bB k - 4) ?_ ?_
  · intro h0
    have := congrArg (nodalParam k) h0
    simp only [map_sub, nodalParam_b, map_ofNat, map_zero] at this
    have := congrArg (eval 0) this
    norm_num at this
  · intro s
    obtain ⟨r, hr⟩ := sq_sub_four_mul_mem_range k s
    change nodalParam k r = _ at hr
    exact ⟨r, by rw [algebraMap_nodal, hr, algebraMap_nodal, map_sub, nodalParam_b, map_ofNat]⟩

instance line_isIntegralClosure :
    IsIntegralClosure (Polynomial k) (NodalRing k) (FractionRing (Polynomial k)) :=
  IsIntegralClosure.of_isIntegrallyClosed _ _ _

/-- The curve `B = Spec k[B]`. -/
abbrev nodalCurve : Scheme.{u} := Spec (.of (NodalRing k))

/-- The normalization map `𝔸¹ → B`, `z ↦ (z², z(z²-4))`. -/
def lineParam : line k ⟶ nodalCurve k :=
  Spec.map (CommRingCat.ofHom (algebraMap (NodalRing k) (Polynomial k)))

instance lineParam_isFinite : IsFinite (lineParam k) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance lineParam_surjective : Surjective (lineParam k) := by
  constructor
  exact (algebraMap_isIntegral_iff.mpr inferInstance :
    (algebraMap (NodalRing k) (Polynomial k)).IsIntegral).comap_surjective
      (nodalParam_injective k)

instance lineParam_isDominant : IsDominant (lineParam k) := inferInstance

/-- `𝔸¹` is the canonical normalization of `B`. -/
def lineNormalizationIso : line k ≅ Palomar.normalization (nodalCurve k) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (IsIntegralClosure.equiv (NodalRing k) (Polynomial k) (FractionRing (Polynomial k))
        (integralClosure (NodalRing k) (FractionRing (Polynomial k)))).toRingEquiv).symm.op ≪≫
    affineNormalizationIso (.of (NodalRing k)) (FractionRing (Polynomial k))

set_option backward.isDefEq.respectTransparency false in
theorem lineNormalizationIso_comm :
    (lineNormalizationIso k).hom ≫ Palomar.normalizationMap (nodalCurve k) = lineParam k := by
  simp only [lineNormalizationIso, Iso.trans_hom, Category.assoc,
    affineNormalizationIso_hom_normalizationMap]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (IsIntegralClosure.equiv (NodalRing k) (Polynomial k) (FractionRing (Polynomial k))
    (integralClosure (NodalRing k) (FractionRing (Polynomial k)))).symm.commutes r

/-! ### The restriction `g` -/

/-- `g* : b ↦ b²`, `d ↦ b³ - 4b`. -/
def gStar : NodalRing k →+* NodalRing k :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp
    (MvPolynomial.aeval ![(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
      MvPolynomial.X 0 ^ 3 - 4 * MvPolynomial.X 0] :
        MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul]
      have : MvPolynomial.aeval ![(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
          MvPolynomial.X 0 ^ 3 - 4 * MvPolynomial.X 0] (nodalRelation k) = 0 := by
        simp only [nodalRelation, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, map_ofNat,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [this, map_zero, mul_zero])

theorem gStar_mk (F : MvPolynomial (Fin 2) k) :
    gStar k (Ideal.Quotient.mk _ F) = Ideal.Quotient.mk _
      (MvPolynomial.aeval ![(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
        MvPolynomial.X 0 ^ 3 - 4 * MvPolynomial.X 0] F) := rfl

@[simp] theorem gStar_b : gStar k (bB k) = bB k ^ 2 := by
  rw [gStar_mk]; simp

@[simp] theorem gStar_d : gStar k (dB k) = bB k ^ 3 - 4 * bB k := by
  rw [gStar_mk]
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero, map_sub, map_mul,
    map_pow, map_ofNat]

theorem gStar_comp_algebraMap :
    (gStar k).comp (algebraMap k (NodalRing k)) = algebraMap k (NodalRing k) := by
  ext a
  change gStar k (Ideal.Quotient.mk _ (MvPolynomial.C a)) = Ideal.Quotient.mk _ (MvPolynomial.C a)
  rw [gStar_mk, MvPolynomial.aeval_C]
  rfl

/-- The squaring map lifts `g`: `ν_B^* ∘ g* = (z ↦ z²) ∘ ν_B^*`. -/
theorem nodalParam_gStar (r : NodalRing k) :
    nodalParam k (gStar k r) = (nodalParam k r).comp (X ^ 2) := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [gStar_mk, nodalParam_mk, nodalParam_mk, comp_eq_aeval, ← AlgHom.comp_apply,
    ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  congr 2
  funext i
  fin_cases i <;> simp [map_ofNat] <;> ring

theorem gStar_injective : Function.Injective (gStar k) := by
  intro a b h
  apply nodalParam_injective k
  have := congrArg (nodalParam k) h
  rw [nodalParam_gStar, nodalParam_gStar, ← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow] at this
  exact expand_injective (by norm_num) this

/-- The actual map `g : B → B`. -/
def gScheme : nodalCurve k ⟶ nodalCurve k := Spec.map (CommRingCat.ofHom (gStar k))

theorem lineSquaring_lineParam : lineSquaring k ≫ lineParam k = lineParam k ≫ gScheme k := by
  unfold lineSquaring lineParam gScheme
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change lineSquaringRing k (nodalParam k r) = nodalParam k (gStar k r)
  rw [nodalParam_gStar]
  simp [lineSquaringRing, expand_eq_comp_X_pow]

theorem line_isIntegralElem_over_g (p : Polynomial k) :
    ((algebraMap (NodalRing k) (Polynomial k)).comp (gStar k)).IsIntegralElem p := by
  let φ := (algebraMap (NodalRing k) (Polynomial k)).comp (gStar k)
  have hX : φ.IsIntegralElem (X : Polynomial k) := by
    refine ⟨Polynomial.X ^ 4 - Polynomial.C (bB k), monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
    change (X : Polynomial k) ^ 4 - nodalParam k (gStar k (bB k)) = 0
    rw [nodalParam_gStar, nodalParam_b]
    simp; ring
  have hC (a : k) : φ.IsIntegralElem (C a) := by
    have h := RingHom.isIntegralElem_map φ (x := algebraMap k (NodalRing k) a)
    have hφ : φ (algebraMap k (NodalRing k) a) = C a := by
      change nodalParam k (gStar k (algebraMap k (NodalRing k) a)) = C a
      rw [← RingHom.comp_apply, gStar_comp_algebraMap, AlgHom.commutes]
      rfl
    rwa [hφ] at h
  have hpow (n : ℕ) : φ.IsIntegralElem ((X : Polynomial k) ^ n) := by
    induction n with
    | zero => simpa using RingHom.isIntegralElem_map φ (x := 1)
    | succ n ih => rw [pow_succ]; exact RingHom.IsIntegralElem.mul φ ih hX
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact RingHom.IsIntegralElem.add φ hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      exact RingHom.IsIntegralElem.mul φ (hC a) (hpow n)

theorem gStar_finite : (gStar k).Finite := by
  refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
  · intro r
    obtain ⟨P, hP, hev⟩ := line_isIntegralElem_over_g k (nodalParam k r)
    refine ⟨P, hP, ?_⟩
    apply nodalParam_injective k
    change algebraMap (NodalRing k) (Polynomial k) (P.eval₂ (gStar k) r) =
      algebraMap (NodalRing k) (Polynomial k) 0
    rw [Polynomial.hom_eval₂, map_zero]
    exact hev
  · apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (NodalRing k))
    rw [gStar_comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

instance gScheme_isFinite : IsFinite (gScheme k) :=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom (gStar k))).mpr (gStar_finite k)

instance gScheme_surjective : Surjective (gScheme k) := by
  constructor
  exact (gStar_finite k).to_isIntegral.comap_surjective (gStar_injective k)

instance gScheme_isDominant : IsDominant (gScheme k) := inferInstance

/-! ### Normalized lift and normalized PCF of `g` -/

instance line_isNormal : IsNormalScheme (line k) := CharZeroPaperSmoothBranch.normal_spec _

/-- `ex:pinched`: the normalized lift of `g` is `z ↦ z²` (transported to the canonical
normalization). -/
theorem line_lift_eq :
    schemeGlobalNormalizationMorphism (gScheme k) =
      (lineNormalizationIso k).inv ≫ lineSquaring k ≫ (lineNormalizationIso k).hom :=
  lift_eq_conj (.of (NodalRing k)) (lineParam k) (lineNormalizationIso k)
    (lineNormalizationIso_comm k) (gScheme k) (lineSquaring k) (lineSquaring_lineParam k)

/-- The structure morphism `B → Spec k`. -/
def nodalStructureMap : nodalCurve k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (NodalRing k)))

instance nodalStructureMap_locallyOfFiniteType : LocallyOfFiniteType (nodalStructureMap k) := by
  unfold nodalStructureMap
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **`ex:pinched`: `g` is PCF for the normalized branch locus.** -/
theorem line_isNormalizedPCF : IsNormalizedPCFOfFiniteType k (nodalStructureMap k) (gScheme k) :=
  isNormalizedPCF_of_conj k (.of (NodalRing k)) (nodalStructureMap k) (lineParam k)
    (lineNormalizationIso k) (lineNormalizationIso_comm k) (gScheme k) (lineSquaring k)
    (lineSquaring_lineParam k) {lineOrigin k} (lineSquaring_reducedFiberBranch k)
    (Set.finite_singleton _) (by rintro D rfl; exact lineSquaring_lineOrigin k)

/-! ### Points of `B` -/

/-- The image in `B` of the point `z = a` of the normalization. -/
def pointOf (a : k) : nodalCurve k :=
  ⟨RingHom.ker ((Polynomial.evalRingHom a).comp (nodalParam k).toRingHom),
    RingHom.ker_isPrime _⟩

theorem mem_pointOf_iff (a : k) (r : NodalRing k) :
    r ∈ (pointOf k a).asIdeal ↔ (nodalParam k r).eval a = 0 := Iff.rfl

theorem lineParam_apply (P : line k) :
    lineParam k P = PrimeSpectrum.comap (nodalParam k).toRingHom P := rfl

theorem pointOf_eq_lineParam (a : k) :
    pointOf k a = lineParam k (primeDivisor (X - C a) (prime_X_sub_C a)).1 := by
  apply PrimeSpectrum.ext
  ext r
  rw [lineParam_apply]
  change _ ↔ nodalParam k r ∈ Ideal.span {X - C a}
  rw [mem_pointOf_iff, Ideal.mem_span_singleton, dvd_iff_isRoot]
  rfl

theorem pointOf_height (a : k) : (pointOf k a).asIdeal.height = 1 := by
  rw [pointOf_eq_lineParam]
  let x : PrimeSpectrum (Polynomial k) := (primeDivisor (X - C a) (prime_X_sub_C a)).1
  have h : x.asIdeal.height = 1 := (idealHeight_eq_coheight (.of (Polynomial k)) x).trans
    (primeDivisor (X - C a) (prime_X_sub_C a)).2
  change (x.asIdeal.under (NodalRing k)).height = 1
  rw [height_under_eq_of_finite_of_finiteType k]
  exact h

/-- `z = a` as an integral effective divisor (a closed point) of the curve `B`. -/
def pointDivisor (a : k) : SchemeDivisorPoint (nodalCurve k) :=
  ⟨pointOf k a, (idealHeight_eq_coheight (.of (NodalRing k)) (pointOf k a)).symm.trans
    (pointOf_height k a)⟩

theorem gScheme_pointOf (a : k) : gScheme k (pointOf k a) = pointOf k (a ^ 2) := by
  apply PrimeSpectrum.ext
  ext r
  change gStar k r ∈ (pointOf k a).asIdeal ↔ r ∈ (pointOf k (a ^ 2)).asIdeal
  rw [mem_pointOf_iff, mem_pointOf_iff, nodalParam_gStar, eval_comp]
  simp

/-- The node: `z = 2` and `z = -2` give the same point `(b,d) = (4,0)`. -/
theorem pointOf_neg_two : pointOf k (-2) = pointOf k 2 := by
  apply PrimeSpectrum.ext
  ext r
  rw [mem_pointOf_iff, mem_pointOf_iff, nodalParam_eval_two]

/-- The node `(b, d) = (4, 0)`. -/
abbrev node : nodalCurve k := pointOf k 2
/-- The point `Q = (b, d) = (16, 48)`. -/
abbrev pointQ : nodalCurve k := pointOf k 4

/-- `g` maps the node to `Q`. -/
theorem gScheme_node : gScheme k (node k) = pointQ k := by
  rw [gScheme_pointOf]; norm_num

/-- The element `d - a(b - 4)`, with image `(z² - 4)(z - a)`. -/
theorem nodalParam_sep (a : k) :
    nodalParam k (dB k - algebraMap k _ a * (bB k - 4)) = (X ^ 2 - 4) * (X - C a) := by
  simp only [map_sub, map_mul, nodalParam_d, nodalParam_b, AlgHom.commutes, map_ofNat]
  rw [Polynomial.algebraMap_eq]
  ring

theorem pointOf_injective_off_node {a c : k} (ha : a ^ 2 ≠ 4)
    (h : pointOf k a = pointOf k c) : a = c := by
  have h1 : dB k - algebraMap k _ a * (bB k - 4) ∈ (pointOf k c).asIdeal := by
    rw [← h, mem_pointOf_iff, nodalParam_sep]; simp
  rw [mem_pointOf_iff, nodalParam_sep] at h1
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_ofNat, mul_eq_zero,
    sub_eq_zero] at h1
  rcases h1 with hc | hc
  · have h2 : dB k - algebraMap k _ c * (bB k - 4) ∈ (pointOf k a).asIdeal := by
      rw [h, mem_pointOf_iff, nodalParam_sep]; simp
    rw [mem_pointOf_iff, nodalParam_sep] at h2
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_ofNat, mul_eq_zero,
      sub_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd h2 ha
    · exact h2
  · exact hc.symm

theorem gScheme_iterate_Q (n : ℕ) :
    (gScheme k)^[n] (pointQ k) = pointOf k ((4 : k) ^ 2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, gScheme_pointOf, ← pow_mul, ← pow_succ]

/-- **The forward orbit of `Q` consists of the distinct points `z = 4^{2^n}`.** -/
theorem orbitQ_injective : Function.Injective fun n : ℕ => (gScheme k)^[n] (pointQ k) := by
  intro n m h
  simp only [gScheme_iterate_Q] at h
  have hne : ((4 : k) ^ 2 ^ n) ^ 2 ≠ 4 := by
    intro h4
    have : (((4 ^ 2 ^ n) ^ 2 : ℕ) : k) = ((4 : ℕ) : k) := by push_cast; exact h4
    have h' := Nat.cast_injective this
    have hle : 4 ≤ 4 ^ 2 ^ n := Nat.le_self_pow (by positivity) 4
    nlinarith
  have := pointOf_injective_off_node k hne h
  have h' : ((4 ^ 2 ^ n : ℕ) : k) = ((4 ^ 2 ^ m : ℕ) : k) := by push_cast; exact this
  exact Nat.pow_right_injective (le_refl 2) (Nat.pow_right_injective (by norm_num : 2 ≤ 4)
    (Nat.cast_injective h'))

/-! ### The fibre of `g` over `Q` -/

/-- The ideal of the point `v` of the plane. -/
def mvPointIdeal (v : Fin 2 → k) : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 - MvPolynomial.C (v 0), MvPolynomial.X 1 - MvPolynomial.C (v 1)}

theorem sub_C_eval_mem (v : Fin 2 → k) (F : MvPolynomial (Fin 2) k) :
    F - MvPolynomial.C (MvPolynomial.eval v F) ∈ mvPointIdeal k v := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    convert Ideal.add_mem _ hp hq using 1
    simp only [map_add]; ring
  | mul_X p i hp =>
    have hi : MvPolynomial.X i - MvPolynomial.C (v i) ∈ mvPointIdeal k v := by
      fin_cases i
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    convert Ideal.add_mem _ (Ideal.mul_mem_right (MvPolynomial.X i) _ hp)
      (Ideal.mul_mem_left _ (MvPolynomial.C (MvPolynomial.eval v p)) hi) using 1
    simp only [map_mul, MvPolynomial.eval_X]
    ring

/-- The ideal of the point `z = a`: `(b - a², d - a(a²-4))`. -/
theorem pointOf_eq_map (a : k) : (pointOf k a).asIdeal =
    (mvPointIdeal k ![a ^ 2, a * (a ^ 2 - 4)]).map
        (Ideal.Quotient.mk (Ideal.span {nodalRelation k})) := by
  apply le_antisymm
  · intro r hr
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [mem_pointOf_iff, eval_nodalParam_mk] at hr
    have := sub_C_eval_mem k ![a ^ 2, a * (a ^ 2 - 4)] F
    rw [hr, map_zero, sub_zero] at this
    exact Ideal.mem_map_of_mem _ this
  · rw [mvPointIdeal, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x (rfl | rfl)
    · change Ideal.Quotient.mk _ _ ∈ (pointOf k a).asIdeal
      rw [mem_pointOf_iff, eval_nodalParam_mk]; simp
    · change Ideal.Quotient.mk _ _ ∈ (pointOf k a).asIdeal
      rw [mem_pointOf_iff, eval_nodalParam_mk]; simp

/-- `g*𝔪_Q` is generated by `b² - 16` and `b³ - 4b - 48`. -/
theorem pointQ_map_gStar : (pointQ k).asIdeal.map (gStar k) =
    (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 - 16,
      MvPolynomial.X 0 ^ 3 - 4 * MvPolynomial.X 0 - 48}).map
        (Ideal.Quotient.mk (Ideal.span {nodalRelation k})) := by
  rw [pointOf_eq_map, mvPointIdeal, Ideal.map_map]
  have : (gStar k).comp (Ideal.Quotient.mk (Ideal.span {nodalRelation k})) =
      (Ideal.Quotient.mk _).comp (MvPolynomial.aeval
        ![(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
          MvPolynomial.X 0 ^ 3 - 4 * MvPolynomial.X 0]).toRingHom := rfl
  rw [this, ← Ideal.map_map, Ideal.map_span, Set.image_pair]
  congr 3
  · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, Matrix.cons_val_zero]
    norm_num [map_ofNat]
  · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, Matrix.cons_val_one, Matrix.cons_val_zero]
    norm_num [map_ofNat]

theorem nodeFiberIdeal_eq_sup :
    Ideal.span {nodalRelation k} ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2 -
      16, MvPolynomial.X 0 ^ 3 - 4 * MvPolynomial.X 0 - 48} =
      CharZeroPaperPinchedCone.nodeFiberIdeal k := by
  rw [← Ideal.span_union]
  unfold CharZeroPaperPinchedCone.nodeFiberIdeal
  congr 1

/-- The fibre ring `k[B]/g*𝔪_Q` is the displayed fibre presentation. -/
def fiberQuotEquiv : (NodalRing k ⧸ (pointQ k).asIdeal.map (gStar k)) ≃+*
    CharZeroPaperPinchedCone.NodeFiber k :=
  (Ideal.quotEquivOfEq (pointQ_map_gStar k)).trans
    ((DoubleQuot.quotQuotEquivQuotSup _ _).trans
      (Ideal.quotEquivOfEq (nodeFiberIdeal_eq_sup k)))

instance pointQ_isMaximal : (pointQ k).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c =>
    ⟨algebraMap k _ c, by simp [AlgHom.commutes]⟩)

/-- At a maximal ideal the fibre ring is the quotient. -/
def fiberRingEquivQuotient {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsMaximal] : m.Fiber S ≃+* S ⧸ m.map (algebraMap R S) := by
  let eκ : (R ⧸ m) ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  let e₁ : m.Fiber S ≃ₐ[R] (R ⧸ m) ⊗[R] S :=
    Algebra.TensorProduct.congr eκ.symm AlgEquiv.refl
  let e₂ : (R ⧸ m) ⊗[R] S ≃ₐ[R] S ⊗[R] (R ⧸ m) := Algebra.TensorProduct.comm R _ _
  let e₃ : S ⊗[R] (R ⧸ m) ≃+* S ⧸ m.map (algebraMap R S) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S m).symm.toRingEquiv
  exact e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃)

/-- The actual fibre ring of `g` over `Q` is `k[d]/(d²)`. -/
def fiberRingQ : (pointQ k).asIdeal.Fiber (SquaringSource (gStar k)) ≃+* DualNumber k :=
  (fiberRingEquivQuotient (S := SquaringSource (gStar k)) (pointQ k).asIdeal).trans ((fiberQuotEquiv k).trans
    (CharZeroPaperPinchedCone.nodeFiberEquivDual (K := k)).toRingEquiv)

/-- **`ex:pinched`: the scheme fibre `g⁻¹(Q)` is `Spec k[d]/(d²)`.** -/
def fiberQ_iso : (gScheme k).fiber (pointQ k) ≅ Spec (.of (DualNumber k)) :=
  Arrow.leftFunc.mapIso
      (Spec.fiberToSpecResidueFieldIso (NodalRing k) (SquaringSource (gStar k)) (pointQ k)) ≪≫
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso (fiberRingQ k)).symm.op

theorem fiberQ_not_isReduced : ¬ IsReduced ((gScheme k).fiber (pointQ k)) := by
  intro h0
  have h := (squaring_fiber_isReduced_iff_ring (φ := gStar k) (pointQ k)).mp h0
  apply CharZeroPaperPinchedCone.nodeFiber_not_isReduced (K := k)
  let e : (pointQ k).asIdeal.Fiber (SquaringSource (gStar k)) ≃+*
      CharZeroPaperPinchedCone.NodeFiber k :=
    (fiberRingEquivQuotient (S := SquaringSource (gStar k)) (pointQ k).asIdeal).trans
      (fiberQuotEquiv k)
  have : _root_.IsReduced ((pointQ k).asIdeal.Fiber (SquaringSource (gStar k))) := h
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- **`Q` lies in the nonreduced-fibre branch locus of `g`.** -/
theorem pointQ_mem_reducedFiberBranch :
    pointDivisor k 4 ∈ schemeReducedFiberBranch (gScheme k) :=
  fiberQ_not_isReduced k

/-- **The fibre over `Q` is supported at the node `(4,0)`.** -/
theorem gScheme_eq_Q_iff (P : nodalCurve k) : gScheme k P = pointQ k ↔ P = node k := by
  constructor
  · intro hP
    have hle : (pointQ k).asIdeal.map (gStar k) ≤ P.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, ← hP]; rfl
    rw [pointQ_map_gStar] at hle
    have hJ : ∀ F ∈ CharZeroPaperPinchedCone.nodeFiberIdeal k,
        Ideal.Quotient.mk (Ideal.span {nodalRelation k}) F ∈ P.asIdeal := by
      intro F hF
      rw [← nodeFiberIdeal_eq_sup] at hF
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hF
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
      exact hle (Ideal.mem_map_of_mem _ hb)
    have hb4 := hJ (MvPolynomial.X 0 - 4) (by
      rw [CharZeroPaperPinchedCone.nodeFiberIdeal_eq]
      exact Ideal.subset_span (by simp))
    have hd2 := hJ (MvPolynomial.X 1 ^ 2) (by
      rw [CharZeroPaperPinchedCone.nodeFiberIdeal_eq]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [map_pow] at hd2
    have hd := P.isPrime.mem_of_pow_mem 2 hd2
    have hle' : (node k).asIdeal ≤ P.asIdeal := by
      rw [pointOf_eq_map, mvPointIdeal, Ideal.map_le_iff_le_comap, Ideal.span_le]
      rintro x (rfl | rfl)
      · change Ideal.Quotient.mk _ _ ∈ P.asIdeal
        convert hb4 using 2; norm_num [map_ofNat]
      · change Ideal.Quotient.mk _ _ ∈ P.asIdeal
        convert hd using 2; norm_num
    have hmax : (node k).asIdeal.IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun c =>
        ⟨algebraMap k _ c, by simp [AlgHom.commutes]⟩)
    exact (PrimeSpectrum.ext (hmax.eq_of_le P.isPrime.ne_top hle')).symm
  · rintro rfl
    exact gScheme_node k

/-! ### `g` is not étale at the node -/

theorem nodalRelation_dual :
    MvPolynomial.aeval ![(4 : DualNumber k), DualNumber.eps] (nodalRelation k) = 0 := by
  simp [nodalRelation, DualNumber.eps_mul_eps, pow_two]

/-- The ring map `k[B] → k[d]/(d²)`, `b ↦ 4`, `d ↦ ε`. -/
def toDual : NodalRing k →+* DualNumber k :=
  Ideal.Quotient.lift _
    (MvPolynomial.aeval ![(4 : DualNumber k), DualNumber.eps]).toRingHom <| by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, nodalRelation_dual,
      mul_zero]

theorem toDual_mk (F : MvPolynomial (Fin 2) k) :
    toDual k (Ideal.Quotient.mk _ F) =
      MvPolynomial.aeval ![(4 : DualNumber k), DualNumber.eps] F := rfl

theorem toDual_d : toDual k (dB k) = DualNumber.eps := by
  rw [toDual_mk]; simp

theorem fst_aeval_dual (F : MvPolynomial (Fin 2) k) :
    (MvPolynomial.aeval ![(4 : DualNumber k), DualNumber.eps] F).fst =
      MvPolynomial.eval ![(4 : k), 0] F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, TrivSqZeroExt.fst_mul, hp, MvPolynomial.eval_X]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [show (4 : DualNumber k) = ((4 : ℕ) : DualNumber k) by norm_cast,
        TrivSqZeroExt.fst_natCast]
      norm_cast
    · simp

theorem fst_toDual (r : NodalRing k) : (toDual k r).fst = (nodalParam k r).eval 2 := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [toDual_mk, fst_aeval_dual, eval_nodalParam_mk]
  congr 2
  funext i
  fin_cases i <;> norm_num

theorem toDual_kills : (pointQ k).asIdeal.map (gStar k) ≤ RingHom.ker (toDual k) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [mem_pointOf_iff, eval_nodalParam_mk] at hr
  change toDual k (gStar k (Ideal.Quotient.mk _ F)) = 0
  rw [gStar_mk, toDual_mk, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hv : (fun i => MvPolynomial.aeval ![(4 : DualNumber k), DualNumber.eps]
      (![(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
        MvPolynomial.X 0 ^ 3 - 4 * MvPolynomial.X 0] i)) =
      (algebraMap k (DualNumber k)) ∘ ![(4 : k) ^ 2, 4 * (4 ^ 2 - 4)] := by
    funext i
    fin_cases i <;> simp [map_ofNat] <;> norm_num
  rw [hv, MvPolynomial.aeval_algebraMap_apply]
  change algebraMap k (DualNumber k) (MvPolynomial.eval _ F) = 0
  rw [hr, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- **`ex:pinched`: `g` is not (formally) étale at the node `(4,0)`, the only point
over `Q`.** -/
theorem node_not_formallyEtale : ¬ ((gScheme k).stalkMap (node k)).hom.FormallyEtale := by
  intro hfe0
  have hfe : ((Spec.map (CommRingCat.ofHom (gStar k))).stalkMap (node k)).hom.FormallyEtale :=
    hfe0
  rw [formallyEtale_respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (gStar k)) (node k))] at hfe
  let S := SquaringSource (gStar k)
  let q : Ideal S := (node k).asIdeal
  have : q.IsPrime := (node k).isPrime
  let p : Ideal (NodalRing k) := q.comap (algebraMap (NodalRing k) S)
  have : q.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have h1 : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q) := hfe
  have h2 : Algebra.IsEtaleAt (NodalRing k) q :=
    Algebra.FormallyEtale.iff_restrictScalars.mpr h1
  have : Module.Finite (NodalRing k) S := gStar_finite k
  have : Algebra.FiniteType (NodalRing k) S := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq (NodalRing k) p q).mp inferInstance).2
  have hd : algebraMap S (Localization.AtPrime q) (dB k) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ q]
    change (nodalParam k (dB k)).eval 2 = 0
    simp; norm_num
  rw [← hmap, IsScalarTower.algebraMap_eq (NodalRing k) S (Localization.AtPrime q),
    ← Ideal.map_map] at hd
  obtain ⟨⟨⟨j, hj⟩, ⟨s, hs⟩⟩, hjs⟩ :=
    (IsLocalization.mem_map_algebraMap_iff q.primeCompl (Localization.AtPrime q)).mp hd
  simp only at hjs
  rw [← map_mul] at hjs
  have hds : (show S from dB k) * s = j :=
    IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors hjs
  have hp : p = (pointQ k).asIdeal := by
    change ((gScheme k) (node k)).asIdeal = _
    rw [gScheme_node]
  have hjker : toDual k j = 0 := by
    have : j ∈ (pointQ k).asIdeal.map (gStar k) := by rw [← hp]; exact hj
    exact toDual_kills k this
  have hs2 : (nodalParam k s).eval 2 ≠ 0 := hs
  have := congrArg (fun x => (toDual k x).snd) hds
  simp only [map_mul, toDual_d, hjker, TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_mul,
    DualNumber.fst_eps, DualNumber.snd_eps, zero_smul, zero_add, fst_toDual] at this
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at this
  exact hs2 (by simpa using this)

/-! ### The unnormalized branch loci and postcritical sets -/

/-- The nonreduced-fibre divisorial branch locus. -/
abbrev nonreducedFibreBranch {X Y : Scheme.{u}} (f : X ⟶ Y) : Set (SchemeDivisorPoint Y) :=
  schemeReducedFiberBranch f

/-- The non-étale divisorial branch locus: images of integral effective divisors at
whose generic point the actual stalk map is not formally étale. -/
def nonEtaleBranch {X Y : Scheme.{u}} (f : X ⟶ Y) : Set (SchemeDivisorPoint Y) :=
  {E | ∃ D ∈ schemeDivisorNonEtaleLocus f, f D.1 = E.1}

/-- `PC(f)` for a branch convention: the generic points of the divisors `fⁿ(E)`,
`E` a branch divisor, `n ≥ 0` (`def:pcf`). -/
def divisorPostcritical {X : Scheme.{u}} (f : X ⟶ X) (B : Set (SchemeDivisorPoint X)) :
    Set X :=
  ⋃ n : ℕ, (f^[n]) '' (Subtype.val '' B)

/-- `Q` lies in the non-étale branch locus of `g`. -/
theorem pointQ_mem_nonEtaleBranch : pointDivisor k 4 ∈ nonEtaleBranch (gScheme k) :=
  ⟨pointDivisor k 2, node_not_formallyEtale k, gScheme_node k⟩

theorem not_finite_of_orbit {B : Set (SchemeDivisorPoint (nodalCurve k))}
    (hB : pointDivisor k 4 ∈ B) : ¬ (divisorPostcritical (gScheme k) B).Finite := by
  intro hfin
  apply Set.infinite_of_injective_forall_mem (orbitQ_injective k) _ hfin
  intro n
  exact Set.mem_iUnion.mpr ⟨n, pointQ k, ⟨pointDivisor k 4, hB, rfl⟩, rfl⟩

/-- **`ex:pinched`: `g` is not PCF for the nonreduced-fibre branch locus.** -/
theorem not_pcf_nonreducedFibre :
    ¬ (divisorPostcritical (gScheme k) (nonreducedFibreBranch (gScheme k))).Finite :=
  not_finite_of_orbit k (pointQ_mem_reducedFiberBranch k)

/-- **`ex:pinched`: `g` is not PCF for the non-étale branch locus.** -/
theorem not_pcf_nonEtale :
    ¬ (divisorPostcritical (gScheme k) (nonEtaleBranch (gScheme k))).Finite :=
  not_finite_of_orbit k (pointQ_mem_nonEtaleBranch k)

end Pcf.Examples.CharZeroPaperPinched

#print axioms Pcf.Examples.CharZeroPaperPinched.nodalParam_injective
#print axioms Pcf.Examples.CharZeroPaperPinched.mem_range_nodalParam_iff
#print axioms Pcf.Examples.CharZeroPaperPinched.lineNormalizationIso_comm
#print axioms Pcf.Examples.CharZeroPaperPinched.gStar_b
#print axioms Pcf.Examples.CharZeroPaperPinched.gStar_d
#print axioms Pcf.Examples.CharZeroPaperPinched.nodalParam_gStar
#print axioms Pcf.Examples.CharZeroPaperPinched.gScheme_isFinite
#print axioms Pcf.Examples.CharZeroPaperPinched.gScheme_surjective
#print axioms Pcf.Examples.CharZeroPaperPinched.line_lift_eq
#print axioms Pcf.Examples.CharZeroPaperPinched.line_isNormalizedPCF
#print axioms Pcf.Examples.CharZeroPaperPinched.gScheme_node
#print axioms Pcf.Examples.CharZeroPaperPinched.orbitQ_injective
#print axioms Pcf.Examples.CharZeroPaperPinched.fiberQ_iso
#print axioms Pcf.Examples.CharZeroPaperPinched.fiberQ_not_isReduced
#print axioms Pcf.Examples.CharZeroPaperPinched.pointQ_mem_reducedFiberBranch
#print axioms Pcf.Examples.CharZeroPaperPinched.gScheme_eq_Q_iff
#print axioms Pcf.Examples.CharZeroPaperPinched.node_not_formallyEtale
#print axioms Pcf.Examples.CharZeroPaperPinched.pointQ_mem_nonEtaleBranch
#print axioms Pcf.Examples.CharZeroPaperPinched.not_pcf_nonreducedFibre
#print axioms Pcf.Examples.CharZeroPaperPinched.not_pcf_nonEtale
