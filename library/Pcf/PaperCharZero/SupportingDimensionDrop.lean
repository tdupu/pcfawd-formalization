/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingDimensionOne
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Exact dimension drop at an integral effective divisor

`paper.tex`, Lemma `lem:restriction` and the sentence before `def:pcfawd`: the
dimension drops by exactly one when passing to an integral effective divisor.

For an integral scheme `X` locally of finite type over a field `k` (no
quasi-compactness is needed) and a codimension-one point `A`, the reduced closure of
`A` satisfies `dim A + 1 = dim X`. More generally `dim Z + codim(Z, X) = dim X` for the
reduced closure `Z` of any point (Stacks 0A21).

The affine input is the dimension formula `ht P + dim B/P = dim B` for a finitely
generated domain `B` over a field. It is proved from Mathlib's Noether normalization,
going up and going down for integral extensions over the normal polynomial ring,
principality of height-one primes in a UFD, Krull's principal ideal theorem, and a
direct computation that a hypersurface in `𝔸^{n+1}` has dimension `n` (Nagata's change of
variables makes its equation monic). The scheme statement then uses the Jacobson
property to compare the dimensions of different affine charts.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u v

open Polynomial

namespace Pcf.PaperCharZero.DimensionDrop

/-- An injective integral extension has the same Krull dimension. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (h : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro P Q hPQ
    have := Ideal.IsIntegral.under_lt_under (R := R) (A := S) (I := P.asIdeal) (J := Q.asIdeal) hPQ
    exact this
  · rw [ringKrullDim, Order.krullDim]
    apply iSup_le
    intro l
    have hker : Ideal.under R (⊥ : Ideal S) ≤ l.head.asIdeal := by
      intro x hx
      have : algebraMap R S x = algebraMap R S 0 := by simpa using hx
      rw [h this]
      exact zero_mem _
    obtain ⟨P, -, hP, hPover⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal S) hker
    have : P.LiesOver l.head.asIdeal := ⟨hPover.symm⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L

/-- Over a nontrivial ring, the quotient by a monic polynomial of positive degree is
an injective integral extension. -/
theorem monic_quotient_injective
    {R : Type u} [CommRing R] [Nontrivial R] {g : R[X]} (hg : g.Monic) (hdeg : 1 ≤ g.natDegree) :
    Function.Injective (algebraMap R (R[X] ⧸ Ideal.span {g})) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  rw [IsScalarTower.algebraMap_apply R R[X] (R[X] ⧸ Ideal.span {g}),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hr
  obtain ⟨q, hq⟩ := hr
  by_contra hr0
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp only [mul_zero, algebraMap_eq, C_eq_zero] at hq
    exact hr0 hq
  have hdeg' := congrArg Polynomial.natDegree hq
  rw [hg.natDegree_mul' (by simpa using hq0)] at hdeg'
  simp only [algebraMap_eq, natDegree_C] at hdeg'
  omega


/-- The polynomial ring in `n` variables over a field has Krull dimension `n`. -/
theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

/-- A hypersurface in affine `(n+1)`-space over a field has Krull dimension `n`.
After Nagata's change of variables the equation is monic in one variable. -/
theorem ringKrullDim_quotient_span_mvPolynomial (k : Type u) [Field k] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) k) (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {f}) = n := by
  classical
  let e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] (MvPolynomial (Fin n) k)[X] :=
    (NoetherNormalization.varChange f).trans (MvPolynomial.finSuccEquiv k n)
  let g : (MvPolynomial (Fin n) k)[X] := e f
  have hu : IsUnit g.leadingCoeff := NoetherNormalization.varChange_leadingCoeff_isUnit f hf0
  let a : MvPolynomial (Fin n) k := ((hu.unit⁻¹ : (MvPolynomial (Fin n) k)ˣ) : _)
  have ha : IsUnit a := Units.isUnit _
  let g' : (MvPolynomial (Fin n) k)[X] := C a * g
  have hmon : g'.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact hu.val_inv_mul
  have hspan : Ideal.span {g'} = Ideal.span {g} :=
    Ideal.span_singleton_mul_left_unit (Polynomial.isUnit_C.mpr ha) g
  have hdeg : 1 ≤ g'.natDegree := by
    rw [natDegree_C_mul_of_isUnit ha]
    by_contra hlt
    have h0 : g.natDegree = 0 := by omega
    have hgC : g = C g.leadingCoeff := by
      rw [leadingCoeff, h0]
      exact eq_C_of_natDegree_eq_zero h0
    apply hfu
    have hgu : IsUnit g := by
      rw [hgC]
      exact Polynomial.isUnit_C.mpr hu
    have : f = e.symm g := by simp [g]
    rw [this]
    exact hgu.map e.symm
  have hmap : Ideal.span {g'} =
      Ideal.map (e.toRingEquiv : _ →+* (MvPolynomial (Fin n) k)[X]) (Ideal.span {f}) := by
    rw [hspan, Ideal.map_span, Set.image_singleton]
    rfl
  let equiv : (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span {f}) ≃+*
      ((MvPolynomial (Fin n) k)[X] ⧸ Ideal.span {g'}) :=
    Ideal.quotientEquiv (Ideal.span {f}) (Ideal.span {g'}) e.toRingEquiv hmap
  rw [ringKrullDim_eq_of_ringEquiv (S := (MvPolynomial (Fin n) k)[X] ⧸ Ideal.span {g'}) equiv]
  have hint := hmon.quotient_isIntegral (I := Ideal.span {g'}) (Ideal.subset_span rfl)
  have : Algebra.IsIntegral (MvPolynomial (Fin n) k)
      ((MvPolynomial (Fin n) k)[X] ⧸ Ideal.span {g'}) := ⟨fun x => hint x⟩
  rw [ringKrullDim_eq_of_isIntegral_of_injective (MvPolynomial (Fin n) k) _
      (monic_quotient_injective hmon hdeg),
    ringKrullDim_mvPolynomial_fin]


/-- In a domain, a nonzero prime has height at least one. -/
theorem one_le_height_of_ne_bot {B : Type v} [CommRing B] [IsDomain B]
    (p : Ideal B) [p.IsPrime] (hp : p ≠ ⊥) : 1 ≤ p.height := by
  have h := Ideal.height_add_one_le_of_lt_of_isPrime (I := (⊥ : Ideal B)) (J := p)
    (bot_lt_iff_ne_bot.mpr hp)
  rwa [Ideal.height_bot, zero_add] at h

/-- **Exact dimension drop, affine form.** For a finitely generated domain over a field,
the quotient by a height-one prime has Krull dimension exactly one less. The proof is
Noether normalization, going down over the normal polynomial ring, principality of
height-one primes in a UFD, and the hypersurface computation. -/
theorem ringKrullDim_quotient_add_one_of_height_eq_one
    (k : Type u) [Field k] (B : Type v) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (p : Ideal B) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (B ⧸ p) + 1 = ringKrullDim B := by
  classical
  obtain ⟨s, φ, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := φ.toRingHom.toAlgebra
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) k) B) := hinj
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨fun x => hint x⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hdimB : ringKrullDim B = s := by
    rw [ringKrullDim_eq_of_isIntegral_of_injective _ B hinj', ringKrullDim_mvPolynomial_fin]
  let q : Ideal (MvPolynomial (Fin s) k) := p.under (MvPolynomial (Fin s) k)
  have hq := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p
  have hq1 : q.height ≤ 1 := by
    rw [← hp, hq]
    exact le_self_add
  have hqne : q ≠ ⊥ := Ideal.IsIntegral.under_ne_bot (R := MvPolynomial (Fin s) k)
    (Ideal.ne_bot_of_height_eq_one hp)
  have hq1' : q.height = 1 := le_antisymm hq1 (one_le_height_of_ne_bot q hqne)
  obtain ⟨f, hfq, hfprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hqne
  have hqspan : q = Ideal.span {f} := Ideal.eq_span_singleton_of_height_eq_one hq1' hfq hfprime
  cases s with
  | zero =>
    exfalso
    apply hfprime.not_isUnit
    let e := MvPolynomial.isEmptyAlgEquiv k (Fin 0)
    have he : e f ≠ 0 := by
      intro h
      exact hfprime.ne_zero (e.injective (by rw [h, map_zero]))
    have hu : IsUnit (e f) := isUnit_iff_ne_zero.mpr he
    have := hu.map e.symm
    simpa using this
  | succ n =>
    letI : Algebra (MvPolynomial (Fin (n + 1)) k ⧸ q) (B ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap le_rfl
    have : Algebra.IsIntegral (MvPolynomial (Fin (n + 1)) k ⧸ q) (B ⧸ p) := by
      infer_instance
    have hinjq : Function.Injective
        (algebraMap (MvPolynomial (Fin (n + 1)) k ⧸ q) (B ⧸ p)) :=
      Ideal.quotientMap_injective
    rw [ringKrullDim_eq_of_isIntegral_of_injective _ _ hinjq, hdimB]
    rw [show ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ q) = n by
      rw [← ringKrullDim_quotient_span_mvPolynomial k n f hfprime.ne_zero hfprime.not_isUnit]
      exact ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hqspan)]
    norm_cast


/-- A strictly monotone map whose image lies strictly above a fixed element raises
heights by at least one. -/
theorem height_add_one_le_of_strictMono_of_forall_lt
    {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (φ : α → β) (hφ : StrictMono φ) (b : β) (hb : ∀ a, b < φ a) (a : α) :
    Order.height a + 1 ≤ Order.height (φ a) := by
  induction h : Order.height a using ENat.recTopCoe with
  | top =>
    have := Order.height_le_height_apply_of_strictMono φ hφ a
    rw [h, top_le_iff] at this
    rw [this]
    exact le_top
  | coe n =>
    obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height a (le_of_eq h.symm)
    let q : LTSeries β := (p.map φ hφ).cons b (by rw [LTSeries.head_map]; exact hb _)
    have hql : q.last = φ a := by
      exact (RelSeries.last_cons _ _ _).trans (by rw [LTSeries.last_map, hlast])
    have hq := Order.length_le_height (p := q) (x := φ a) hql.le
    have hlen' : q.length = n + 1 := by
      exact (RelSeries.cons_length _ _ _).trans (by rw [LTSeries.map_length, hlen])
    rw [hlen'] at hq
    exact_mod_cast hq

/-- The Krull dimension of the quotient by a prime is the coheight of that prime. -/
theorem ringKrullDim_quotient_eq_coheight {B : Type v} [CommRing B]
    (P : Ideal B) [P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum B) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  congr 1

/-- Height plus dimension of the quotient never exceeds the dimension. -/
theorem height_add_ringKrullDim_quotient_le {B : Type v} [CommRing B]
    (P : Ideal B) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by
  haveI : Nonempty (PrimeSpectrum B) := ⟨⟨P, inferInstance⟩⟩
  rw [ringKrullDim_quotient_eq_coheight, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty,
    PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum B), ← WithBot.coe_add]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a : PrimeSpectrum B =>
    Order.height a + Order.coheight a) ⟨P, inferInstance⟩)

/-- Passing to the quotient by a nonzero prime `P₁ ≤ P` of a domain lowers the height
of `P` by at least one. -/
theorem height_map_quotient_add_one_le {B : Type v} [CommRing B] [IsDomain B]
    (P₁ P : Ideal B) [P₁.IsPrime] [P.IsPrime] [(P.map (Ideal.Quotient.mk P₁)).IsPrime]
    (hP₁ : P₁ ≠ ⊥) (hle : P₁ ≤ P) :
    (P.map (Ideal.Quotient.mk P₁)).height + 1 ≤ P.height := by
  let φ := PrimeSpectrum.comap (Ideal.Quotient.mk P₁)
  have hφ : StrictMono φ := RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  have hb : ∀ a : PrimeSpectrum (B ⧸ P₁), (⊥ : PrimeSpectrum B) < φ a := by
    intro a
    have hle' : P₁ ≤ (φ a).asIdeal := by
      have : RingHom.ker (Ideal.Quotient.mk P₁) ≤ Ideal.comap (Ideal.Quotient.mk P₁) a.asIdeal :=
        Ideal.comap_mono bot_le
      rwa [Ideal.mk_ker] at this
    refine lt_of_le_of_ne bot_le fun h => hP₁ (le_bot_iff.mp ?_)
    rw [← h] at hle'
    exact hle'
  have hφP : φ ⟨P.map (Ideal.Quotient.mk P₁), inferInstance⟩ = ⟨P, inferInstance⟩ := by
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hle]
  have h := height_add_one_le_of_strictMono_of_forall_lt φ hφ ⊥ hb
    ⟨P.map (Ideal.Quotient.mk P₁), inferInstance⟩
  rw [hφP] at h
  have e1 := PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum B)
  have e2 := PrimeSpectrum.height_eq_orderHeight
    (⟨P.map (Ideal.Quotient.mk P₁), inferInstance⟩ : PrimeSpectrum (B ⧸ P₁))
  rw [← e1, ← e2] at h
  exact h

/-- A cancellation step in `WithBot ℕ∞`. -/
theorem exists_eq_of_add_one_eq_natCast {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = N) :
    ∃ M : ℕ, N = M + 1 ∧ d = M := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [this] at h
      exact absurd (WithBot.coe_injective h) (ENat.top_ne_natCast N)
    | coe m =>
      refine ⟨m, ?_, rfl⟩
      have : ((m + 1 : ℕ) : WithBot ℕ∞) = (N : WithBot ℕ∞) := by
        rw [← h]
        norm_cast
      exact_mod_cast this.symm

/-- Finitely generated algebras over a field have finite Krull dimension. -/
theorem exists_ringKrullDim_eq_natCast (k : Type u) [Field k] (B : Type v) [CommRing B]
    [Nontrivial B] [Algebra k B] [Algebra.FiniteType k B] :
    ∃ N : ℕ, ringKrullDim B = N := by
  obtain ⟨s, φ, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := φ.toRingHom.toAlgebra
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) k) B) := hinj
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨fun x => hint x⟩
  exact ⟨s, by
    rw [ringKrullDim_eq_of_isIntegral_of_injective _ B hinj', ringKrullDim_mvPolynomial_fin]⟩

/-- **Dimension formula** for a finitely generated domain over a field:
`ht P + dim (B/P) = dim B` for every prime `P`. -/
theorem height_add_ringKrullDim_quotient_eq (k : Type u) [Field k] :
    ∀ (N : ℕ) (B : Type v) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B],
      ringKrullDim B = N → ∀ (P : Ideal B) [P.IsPrime],
        (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by
  intro N
  induction N with
  | zero =>
    intro B _ _ _ _ hN P _
    apply le_antisymm (height_add_ringKrullDim_quotient_le P)
    by_cases hP0 : P = ⊥
    · subst hP0
      rw [Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot B)]
      simp
    · exfalso
      have h1 := one_le_height_of_ne_bot P hP0
      have h2 := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := P))
      rw [hN] at h2
      have : ((1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
        (WithBot.coe_le_coe.mpr h1).trans h2
      norm_cast at this
  | succ M ih =>
    intro B _ _ _ _ hN P _
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
    apply le_antisymm (height_add_ringKrullDim_quotient_le P)
    by_cases hP0 : P = ⊥
    · subst hP0
      rw [Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot B)]
      simp
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    obtain ⟨P₁, hP₁min, hP₁le⟩ :=
      Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem P).mpr hxP)
    have : P₁.IsPrime := hP₁min.1.1
    have hxP₁ : x ∈ P₁ := (Ideal.span_singleton_le_iff_mem P₁).mp hP₁min.1.2
    have hP₁ne : P₁ ≠ ⊥ := fun h => hx0 (by rw [h] at hxP₁; exact hxP₁)
    have hP₁ht : P₁.height = 1 := le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P₁ hP₁min)
      (one_le_height_of_ne_bot P₁ hP₁ne)
    have hdrop := ringKrullDim_quotient_add_one_of_height_eq_one k B P₁ hP₁ht
    rw [hN] at hdrop
    obtain ⟨M', hM', hdimB₁⟩ := exists_eq_of_add_one_eq_natCast hdrop
    have hMM : M' = M := by omega
    subst hMM
    have : (P.map (Ideal.Quotient.mk P₁)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    have hih := ih (B ⧸ P₁) hdimB₁ (P.map (Ideal.Quotient.mk P₁))
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hP₁le), hdimB₁] at hih
    have hF := height_map_quotient_add_one_le P₁ P hP₁ne hP₁le
    rw [hN]
    push_cast
    rw [← hih]
    calc ((P.map (Ideal.Quotient.mk P₁)).height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) + 1
        = (((P.map (Ideal.Quotient.mk P₁)).height + 1 : ℕ∞) : WithBot ℕ∞) +
            ringKrullDim (B ⧸ P) := by
          rw [WithBot.coe_add, WithBot.coe_one, add_right_comm]
      _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
          gcongr
          exact WithBot.coe_le_coe.mpr hF


/-- In a finitely generated domain over a field every maximal ideal has height equal to
the Krull dimension. -/
theorem height_eq_ringKrullDim_of_isMaximal (k : Type u) [Field k] (B : Type v) [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨N, hN⟩ := exists_ringKrullDim_eq_natCast k B
  have h := height_add_ringKrullDim_quotient_eq k N B hN m
  letI := Ideal.Quotient.field m
  rwa [ringKrullDim_eq_zero_of_field, add_zero] at h

/-- A nonzero element of a finitely generated domain over a field avoids some maximal
ideal (the Jacobson property). -/
theorem exists_isMaximal_notMem (k : Type u) [Field k] (B : Type v) [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] {g : B} (hg : g ≠ 0) :
    ∃ m : Ideal B, m.IsMaximal ∧ g ∉ m := by
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  by_contra h
  push Not at h
  have hj : (⊥ : Ideal B).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› (Ideal.isPrime_bot.isRadical)
  apply hg
  have hmem : g ∈ (⊥ : Ideal B).jacobson := Ideal.mem_sInf.mpr fun J hJ => h J hJ.2
  rw [hj] at hmem
  exact hmem

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

/-- The coheight of a point of an affine open is the height of its prime. -/
theorem coheight_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : Spec Γ(X, U)) : Order.coheight (hU.fromSpec p) = p.asIdeal.height := by
  rw [coheight_eq_of_isOpenImmersion, idealHeight_eq_coheight]

/-- The dimension of the quotient by the prime of a point bounds the height of that
point in the ambient scheme. -/
theorem ringKrullDim_quotient_le_height_fromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (p : Spec Γ(X, U)) :
    ringKrullDim (Γ(X, U) ⧸ p.asIdeal) ≤ Order.height (hU.fromSpec p) := by
  have hstrict : StrictMono (fun q : Spec Γ(X, U) => hU.fromSpec q) := by
    letI := specializationOrder (Spec Γ(X, U))
    letI := specializationOrder X
    exact hU.fromSpec.continuous.specialization_monotone.strictMono_of_injective
      hU.fromSpec.isOpenEmbedding.injective
  have h1 := Order.height_le_height_apply_of_strictMono _ hstrict p
  haveI := p.isPrime
  have h2 : Order.height p =
      Order.coheight (⟨p.asIdeal, p.isPrime⟩ : PrimeSpectrum Γ(X, U)) := by
    rw [← Order.height_orderIso (specOrderIsoPrimeSpectrum Γ(X, U)) p,
      specOrderIsoPrimeSpectrum_apply]
    exact Order.height_toDual (α := PrimeSpectrum Γ(X, U)) p
  rw [ringKrullDim_quotient_eq_coheight]
  rw [h2] at h1
  exact_mod_cast h1


/-- The generic point lies in every nonempty open. -/
theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [h : Nonempty U] :
    genericPoint X ∈ U := by
  change genericPoint X ∈ (U : Set X)
  rw [(genericPoint_spec X).mem_open_set_iff U.isOpen]
  obtain ⟨x⟩ := h
  exact ⟨x.1, Set.mem_univ _, x.2⟩

section Scheme

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]

include k s

/-- All nonempty affine opens of an integral scheme locally of finite type over a field
have the same coordinate-ring dimension; here is one inequality. -/
theorem ringKrullDim_le_of_affineOpens (U V : X.affineOpens)
    [Nonempty (U : X.Opens)] [Nonempty (V : X.Opens)] :
    ringKrullDim Γ(X, V) ≤ ringKrullDim Γ(X, U) := by
  letI := Pcf.schemeAffineAlgebraOfField k s V
  have := Pcf.schemeAffineAlgebraOfField_finiteType k s V
  have hηU := genericPoint_mem_of_nonempty (U : X.Opens)
  have hηV := genericPoint_mem_of_nonempty (V : X.Opens)
  obtain ⟨g, hgle, hηg⟩ := V.2.exists_basicOpen_le (V := (U : X.Opens) ⊓ V)
    ⟨genericPoint X, ⟨hηU, hηV⟩⟩ hηV
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hηg
    exact hηg
  obtain ⟨m, hm, hgm⟩ := exists_isMaximal_notMem k Γ(X, V) hg0
  let pm : Spec Γ(X, V) := (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(X, V))
  have hzg : V.2.fromSpec pm ∈ X.basicOpen g := by
    have : pm ∈ V.2.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [V.2.fromSpec_preimage_basicOpen]
      exact hgm
    exact this
  have hzU : V.2.fromSpec pm ∈ (U : X.Opens) := (hgle hzg).1
  have hcoh : (Order.coheight (V.2.fromSpec pm) : WithBot ℕ∞) = ringKrullDim Γ(X, V) := by
    rw [coheight_fromSpec (U := (V : X.Opens)) V.2 pm]
    exact height_eq_ringKrullDim_of_isMaximal k _ m
  obtain ⟨q, hq⟩ : V.2.fromSpec pm ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    exact hzU
  rw [← hcoh, ← hq, coheight_fromSpec (U := (U : X.Opens)) U.2 q]
  exact Ideal.height_le_ringKrullDim_of_ne_top q.isPrime.ne_top

/-- The order-theoretic dimension of the scheme is bounded by the dimension of any
nonempty affine coordinate ring. -/
theorem krullDim_le_ringKrullDim (U : X.affineOpens) [Nonempty (U : X.Opens)] :
    Order.krullDim X ≤ ringKrullDim Γ(X, U) := by
  rw [Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V' : X.affineOpens := ⟨V, hV⟩
  have : Nonempty (V' : X.Opens) := ⟨⟨x, hxV⟩⟩
  have hVU := ringKrullDim_le_of_affineOpens k s U V'
  have hV' : IsAffineOpen V := hV
  have hx : hV'.fromSpec (hV'.primeIdealOf ⟨x, hxV⟩) = x := hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hc := coheight_fromSpec hV' (hV'.primeIdealOf ⟨x, hxV⟩)
  rw [hx] at hc
  rw [hc]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top inferInstance)).trans hVU

/-- Order-theoretic exact dimension drop at a codimension-one point. -/
theorem height_add_one_eq_krullDim (A : SchemeDivisorPoint X) :
    (Order.height A.1 : WithBot ℕ∞) + 1 = Order.krullDim X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hAU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ A.1) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have : Nonempty (U' : X.Opens) := ⟨⟨A.1, hAU⟩⟩
  letI := Pcf.schemeAffineAlgebraOfField k s U'
  have := Pcf.schemeAffineAlgebraOfField_finiteType k s U'
  let p := hU.primeIdealOf ⟨A.1, hAU⟩
  have hpA : hU.fromSpec p = A.1 := hU.fromSpec_primeIdealOf _
  have hp1 : p.asIdeal.height = 1 := by
    rw [← coheight_fromSpec hU p, hpA]
    exact A.2
  have := p.isPrime
  have hdrop := ringKrullDim_quotient_add_one_of_height_eq_one k Γ(X, U) p.asIdeal hp1
  have hle := ringKrullDim_quotient_le_height_fromSpec hU p
  rw [hpA] at hle
  have hX := krullDim_le_ringKrullDim k s U'
  apply le_antisymm
  · have : Nonempty X := ⟨A.1⟩
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    have h := le_iSup (fun a : X => Order.height a + Order.coheight a) A.1
    simp only [A.2] at h
    exact_mod_cast h
  · calc Order.krullDim X ≤ ringKrullDim Γ(X, U) := hX
      _ = ringKrullDim (Γ(X, U) ⧸ p.asIdeal) + 1 := hdrop.symm
      _ ≤ (Order.height A.1 : WithBot ℕ∞) + 1 := by gcongr

/-- **Dimension formula** (Stacks 0A21) at every point: for an integral scheme locally of
finite type over a field, `height x + coheight x = dim X` in the specialization order. -/
theorem height_add_coheight_eq_krullDim (x : X) :
    ((Order.height x + Order.coheight x : ℕ∞) : WithBot ℕ∞) = Order.krullDim X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have : Nonempty (U' : X.Opens) := ⟨⟨x, hxU⟩⟩
  letI := Pcf.schemeAffineAlgebraOfField k s U'
  have := Pcf.schemeAffineAlgebraOfField_finiteType k s U'
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf _
  have hcoh : Order.coheight x = p.asIdeal.height := by
    rw [← coheight_fromSpec hU p, hpx]
  have := p.isPrime
  obtain ⟨N, hN⟩ := exists_ringKrullDim_eq_natCast k Γ(X, U)
  have hform := height_add_ringKrullDim_quotient_eq k N Γ(X, U) hN p.asIdeal
  have hle := ringKrullDim_quotient_le_height_fromSpec hU p
  rw [hpx] at hle
  have hX := krullDim_le_ringKrullDim k s U'
  apply le_antisymm
  · have : Nonempty X := ⟨x⟩
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr
      (le_iSup (fun a : X => Order.height a + Order.coheight a) x)
  · calc Order.krullDim X ≤ ringKrullDim Γ(X, U) := hX
      _ = (p.asIdeal.height : WithBot ℕ∞) + ringKrullDim (Γ(X, U) ⧸ p.asIdeal) := hform.symm
      _ ≤ (p.asIdeal.height : WithBot ℕ∞) + (Order.height x : WithBot ℕ∞) := by gcongr
      _ = ((Order.height x + Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
          rw [hcoh, WithBot.coe_add, add_comm]

end Scheme

/-- For every scheme the order-theoretic Krull dimension of the specialization order
equals the topological Krull dimension. -/
theorem scheme_krullDim_eq_topologicalKrullDim (Y : Scheme.{u}) :
    Order.krullDim Y = topologicalKrullDim Y := by
  rw [topologicalKrullDim]
  exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))).symm

/-- The reduced closure of a point has topological dimension equal to the height of the
point in the specialization order. -/
theorem topologicalKrullDim_pointClosure {X : Scheme.{u}} (x : X) :
    topologicalKrullDim (pointClosureIdealSheaf x).subscheme = Order.height x := by
  let I := pointClosureIdealSheaf x
  let ι := I.subschemeι
  rw [← scheme_krullDim_eq_topologicalKrullDim, Order.height_eq_krullDim_Iic]
  let e : I.subscheme ↪o X :=
    { toFun := ι
      inj' := ι.isClosedEmbedding.injective
      map_rel_iff' := fun {a b} => by
        change ι b ⤳ ι a ↔ b ⤳ a
        exact ι.isClosedEmbedding.isInducing.specializes_iff }
  have hrange : Set.range e = Set.Iic x := by
    ext y
    change y ∈ Set.range ι ↔ x ⤳ y
    rw [Scheme.IdealSheafData.range_subschemeι]
    change y ∈ ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ({x} : Set X), isClosed_closure⟩).support : Set X) ↔ x ⤳ y
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact specializes_iff_mem_closure.symm
  exact Order.krullDim_eq_of_orderIso (e.orderIso.trans (Set.orderIsoOfEq _ _ hrange))


/-- **Exact dimension drop** (`lem:restriction`, sentence before `def:pcfawd`): for an
integral scheme locally of finite type over a field, the reduced closure of every
integral effective divisor has dimension exactly one less than the ambient scheme.

Manuscript: `lem:restriction` (Lemma 3.2). -/
theorem divisorClosure_dimension_add_one_eq
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (A : SchemeDivisorPoint X) :
    topologicalKrullDim (pointClosureIdealSheaf A.1).subscheme + 1 = topologicalKrullDim X := by
  rw [topologicalKrullDim_pointClosure, ← scheme_krullDim_eq_topologicalKrullDim]
  exact height_add_one_eq_krullDim k s A

/-- The codimension formula `dim X = dim Z + codim(Z, X)` for the reduced closure `Z` of
any point of an integral scheme locally of finite type over a field. -/
theorem pointClosure_dimension_add_codim_eq
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (x : X) :
    topologicalKrullDim (pointClosureIdealSheaf x).subscheme + (Order.coheight x : WithBot ℕ∞) =
      topologicalKrullDim X := by
  rw [topologicalKrullDim_pointClosure, ← scheme_krullDim_eq_topologicalKrullDim,
    ← height_add_coheight_eq_krullDim k s x, WithBot.coe_add]

/-- Dimension-indexed form: if `dim X = n + 1`, every divisor closure has dimension `n`. -/
theorem divisorClosure_dimension_eq_of_dimension_eq_succ
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (A : SchemeDivisorPoint X) (n : ℕ)
    (hX : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (pointClosureIdealSheaf A.1).subscheme = (n : WithBot ℕ∞) := by
  have h := divisorClosure_dimension_add_one_eq k s A
  rw [hX] at h
  obtain ⟨M, hM, hd⟩ := exists_eq_of_add_one_eq_natCast h
  rw [hd]
  congr 1
  omega

end Pcf.PaperCharZero.DimensionDrop

#print axioms Pcf.PaperCharZero.DimensionDrop.ringKrullDim_quotient_add_one_of_height_eq_one
#print axioms Pcf.PaperCharZero.DimensionDrop.height_add_ringKrullDim_quotient_eq
#print axioms Pcf.PaperCharZero.DimensionDrop.height_add_coheight_eq_krullDim
#print axioms Pcf.PaperCharZero.DimensionDrop.divisorClosure_dimension_add_one_eq
#print axioms Pcf.PaperCharZero.DimensionDrop.pointClosure_dimension_add_codim_eq
#print axioms Pcf.PaperCharZero.DimensionDrop.divisorClosure_dimension_eq_of_dimension_eq_succ
