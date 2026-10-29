/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CharPExceptionalNormalZ
public import Pcf.Examples.PaperP.CharPExceptionalFibre
public import Pcf.Examples.PaperP.CharPExceptionalLocalQuotient
public import Pcf.Vendor.RegularLocalization.MaximalCohenMacaulay
public import Pcf.Vendor.RegularLocalization.RegularLocalRingBasic
public import Pcf.Bounding.FiniteTypeRegularLocus
public import Pcf.Stacks.Common.EtaleRegular
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# `ex:charp-exceptional-fibre-paper`: singular locus and Cohen–Macaulayness

For `X = Spec k[x,y,z,t]/(x^p - t y^p - z^(p+1))` in characteristic `p` and
`A = V(x,y,z)`:

* `stalkSingularLocus X = A` (`hyper_stalkSingularLocus_eq`);
* `R = k[x,y,z,t]/(f)` is a Cohen–Macaulay ring (`hyperRing_isCohenMacaulayRing`).

Regularity off `A`: on `y ≠ 0`, `R_y ≅ k[x,y,z]_y`; on `z ≠ 0`, `R_z` is étale over
`k[x,y,t]` (`rz_etale`), hence regular (no perfectness of `k` is needed). Off these two
opens, `x^p = t y^p + z^(p+1)` forces `x = 0`. Singularity on `A`: `R_𝔮 ≅ S/(f)` with
`S = k[x,y,z,t]_Q` regular local and `f ∈ 𝔪_S^2`, so `S/(f)` is not regular.
Cohen–Macaulay: `S` regular ⇒ Cohen–Macaulay, and `f` is a nonzerodivisor in `𝔪_S`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CharPExceptionalSingular

open MvPolynomial IsLocalRing
open Pcf.Examples.PaperP.CharPExceptionalBlowup Pcf.Examples.PaperP.CharPExceptionalNormal
  Pcf.Examples.PaperP.CharPExceptionalLocal

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

variable (k : Type u) [Field k] (p : ℕ)

/-- `f = x^p - t y^p - z^(p+1)` is nonzero (for `p > 0`). -/
theorem hyperEquation_ne_zero (hp : 0 < p) : hyperEquation k p ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval ![0, 0, 1, 0]) h
  simp [hyperEquation, zero_pow hp.ne'] at this

variable (𝔮 : Ideal (HyperRing k p)) [𝔮.IsPrime]

/-- The ambient local ring `S = k[x,y,z,t]_Q`. -/
abbrev AmbLoc := Localization.AtPrime (liftPrime (hyperEquation k p) 𝔮)

/-- The image of `f` in `S`. -/
noncomputable abbrev fLoc : AmbLoc k p 𝔮 :=
  algebraMap (Ambient k) (AmbLoc k p 𝔮) (hyperEquation k p)

omit [𝔮.IsPrime] in
theorem hyperEquation_mem_liftPrime : hyperEquation k p ∈ liftPrime (hyperEquation k p) 𝔮 := by
  change Ideal.Quotient.mk _ _ ∈ 𝔮
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
  exact 𝔮.zero_mem

theorem fLoc_mem_maximalIdeal : fLoc k p 𝔮 ∈ maximalIdeal (AmbLoc k p 𝔮) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _).mpr (hyperEquation_mem_liftPrime k p 𝔮)

theorem fLoc_ne_zero (hp : 0 < p) : fLoc k p 𝔮 ≠ 0 := by
  have hinj : Function.Injective (algebraMap (Ambient k) (AmbLoc k p 𝔮)) :=
    IsLocalization.injective _ (liftPrime (hyperEquation k p) 𝔮).primeCompl_le_nonZeroDivisors
  exact (map_ne_zero_iff _ hinj).mpr (hyperEquation_ne_zero k p hp)

theorem fLoc_isSMulRegular (hp : 0 < p) : IsSMulRegular (AmbLoc k p 𝔮) (fLoc k p 𝔮) :=
  IsSMulRegular.of_ne_zero (fLoc_ne_zero k p 𝔮 hp)

/-- `S = k[x,y,z,t]_Q` is a regular local ring. -/
instance ambLoc_isRegularLocalRing : IsRegularLocalRing (AmbLoc k p 𝔮) := inferInstance

/-- **Cohen–Macaulay at every prime.** -/
theorem localization_isCohenMacaulayLocalRing (hp : 0 < p) :
    Pcf.Vendor.IsCohenMacaulayLocalRing (Localization.AtPrime 𝔮) := by
  haveI : Pcf.Vendor.IsCohenMacaulayLocalRing (AmbLoc k p 𝔮) :=
    Pcf.Vendor.isCohenMacaulayLocalRing_of_isRegularLocalRing
  haveI : Pcf.Vendor.IsCohenMacaulayLocalRing
      (AmbLoc k p 𝔮 ⧸ Ideal.span {fLoc k p 𝔮}) :=
    (Pcf.Vendor.quotient_span_isSMulRegular_isCohenMacaulay_iff_isCohenMacaulay (AmbLoc k p 𝔮) _
      (fLoc_isSMulRegular k p 𝔮 hp) (fLoc_mem_maximalIdeal k p 𝔮)).mp inferInstance
  exact Pcf.Vendor.isCohenMacaulayLocalRing_of_ringEquiv
    (localizationQuotientEquiv (hyperEquation k p) 𝔮).symm

/-- **`ex:charp-exceptional-fibre-paper`: the hypersurface ring is Cohen–Macaulay.**

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem hyperRing_isCohenMacaulayRing (hp : 0 < p) :
    Pcf.Vendor.IsCohenMacaulayRing (HyperRing k p) :=
  (Pcf.Vendor.isCohenMacaulayRing_def _).mpr fun 𝔮 _ =>
    localization_isCohenMacaulayLocalRing k p 𝔮 hp

/-- If `x, y, z ∈ 𝔮` then `f ∈ 𝔪_S^2` (here `p ≥ 2`). -/
theorem fLoc_mem_sq (hp : 2 ≤ p) (hx : hx k p ∈ 𝔮) (hy : hy k p ∈ 𝔮) (hz : hz k p ∈ 𝔮) :
    fLoc k p 𝔮 ∈ maximalIdeal (AmbLoc k p 𝔮) ^ 2 := by
  have hmem : ∀ i : Fin 4, Ideal.Quotient.mk (Ideal.span {hyperEquation k p}) (X i) ∈ 𝔮 →
      algebraMap (Ambient k) (AmbLoc k p 𝔮) (X i) ∈ maximalIdeal (AmbLoc k p 𝔮) := fun i h =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (liftPrime (hyperEquation k p) 𝔮) _).mpr h
  have h0 := hmem 0 hx
  have h1 := hmem 1 hy
  have h2 := hmem 2 hz
  set m := maximalIdeal (AmbLoc k p 𝔮)
  have hpow : ∀ (a : AmbLoc k p 𝔮) (n : ℕ), a ∈ m → 2 ≤ n → a ^ n ∈ m ^ 2 := fun a n ha hn =>
    Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha n)
  simp only [fLoc, hyperEquation, map_sub, map_mul, map_pow]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ (hpow _ _ h0 hp) ?_) (hpow _ _ h2 (by omega))
  exact Ideal.mul_mem_left _ _ (hpow _ _ h1 hp)

/-- **Singular along `A`.** If `x, y, z ∈ 𝔮`, the local ring `R_𝔮` is not regular. -/
theorem not_isRegularLocalRing_of_mem (hp : 2 ≤ p)
    (hx : hx k p ∈ 𝔮) (hy : hy k p ∈ 𝔮) (hz : hz k p ∈ 𝔮) :
    ¬ IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  intro hreg
  have hreg' : IsRegularLocalRing (AmbLoc k p 𝔮 ⧸ Ideal.span {fLoc k p 𝔮}) :=
    IsRegularLocalRing.of_ringEquiv (localizationQuotientEquiv (hyperEquation k p) 𝔮)
  have hmem := fLoc_mem_maximalIdeal k p 𝔮
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (fLoc_isSMulRegular k p 𝔮 (by omega)) hmem
  have sub : ((({fLoc k p 𝔮} : Finset (AmbLoc k p 𝔮)) : Set (AmbLoc k p 𝔮))) ⊆
      maximalIdeal (AmbLoc k p 𝔮) := by simpa using hmem
  have h3 : IsRegularLocalRing (AmbLoc k p 𝔮 ⧸
        Ideal.span ((({fLoc k p 𝔮} : Finset (AmbLoc k p 𝔮)) : Set (AmbLoc k p 𝔮)))) ∧
      ringKrullDim (AmbLoc k p 𝔮 ⧸
        Ideal.span ((({fLoc k p 𝔮} : Finset (AmbLoc k p 𝔮)) : Set (AmbLoc k p 𝔮)))) +
        (({fLoc k p 𝔮} : Finset (AmbLoc k p 𝔮)).card : WithBot ℕ∞) =
        ringKrullDim (AmbLoc k p 𝔮) := by
    rw [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one]
    exact ⟨hreg', hdim⟩
  have hli := ((Pcf.Vendor.quotient_isRegularLocalRing_tfae (AmbLoc k p 𝔮)
    {fLoc k p 𝔮} sub).out 3 2).mp h3
  have hne := hli.ne_zero (⟨fLoc k p 𝔮, by simp⟩ :
    ((({fLoc k p 𝔮} : Finset (AmbLoc k p 𝔮)) : Set (AmbLoc k p 𝔮))))
  apply hne
  change (maximalIdeal (AmbLoc k p 𝔮)).toCotangent ⟨fLoc k p 𝔮, hmem⟩ = 0
  rw [Ideal.toCotangent_eq_zero]
  exact fLoc_mem_sq k p 𝔮 hp hx hy hz

/-- `R_y` is a regular ring (`R_y ≅ k[x,y,z]_y`). -/
theorem ry_isRegularRing : IsRegularRing (Ry k p) := by
  haveI : IsRegularRing (Ay k) :=
    Pcf.isRegularRing_of_isLocalization (Submonoid.powers (X 1 : Aff k)) (Ay k)
  exact IsRegularRing.of_ringEquiv (ryEquiv k p).symm

/-- `R_z` is a regular ring (étale over `k[x,y,t]`). -/
theorem rz_isRegularRing [Fact p.Prime] [CharP k p] : IsRegularRing (Rz k p) := by
  letI : Algebra (B0 k) (Rz k p) := (b0ToRz k p).toAlgebra
  haveI := rz_etale k p
  exact Pcf.Stacks.isRegularRing_of_etale (B0 k) (Rz k p)

/-- If `s ∉ 𝔮` and `R_s` is a regular ring then `R_𝔮` is regular. -/
theorem isRegularLocalRing_of_away {s : HyperRing k p} (hs : s ∉ 𝔮)
    (hreg : IsRegularRing (Localization.Away s)) :
    IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  have hdisj : Disjoint ((Submonoid.powers s) : Set (HyperRing k p)) 𝔮 :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hs
  let q := 𝔮.map (algebraMap (HyperRing k p) (Localization.Away s))
  haveI : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers s) _ _ inferInstance hdisj
  have hq : q.comap (algebraMap (HyperRing k p) (Localization.Away s)) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers s) _ inferInstance hdisj
  have h := (Pcf.isRegularLocalRing_localizationAtPrime_iff (.powers s) (Localization.Away s) q).mp
    inferInstance
  have transfer (q' : Ideal (HyperRing k p)) [q'.IsPrime] (h : q' = 𝔮)
      (hr : IsRegularLocalRing (Localization.AtPrime q')) :
      IsRegularLocalRing (Localization.AtPrime 𝔮) := by
    subst q'
    exact hr
  exact transfer _ hq h

/-- **Regular off `A`.** -/
theorem isRegularLocalRing_iff_not_mem [Fact p.Prime] [CharP k p] :
    IsRegularLocalRing (Localization.AtPrime 𝔮) ↔
      ¬ (hx k p ∈ 𝔮 ∧ hy k p ∈ 𝔮 ∧ hz k p ∈ 𝔮) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  constructor
  · rintro hreg ⟨hx', hy', hz'⟩
    exact not_isRegularLocalRing_of_mem k p 𝔮 hp2 hx' hy' hz' hreg
  · intro hnot
    by_cases hy' : hy k p ∈ 𝔮
    · by_cases hz' : hz k p ∈ 𝔮
      · exfalso
        apply hnot
        refine ⟨?_, hy', hz'⟩
        have hrel := hyper_relation k p
        have : hx k p ^ p ∈ 𝔮 := by
          have : hx k p ^ p = ht k p * hy k p ^ p + hz k p ^ (p + 1) := by
            linear_combination hrel
          rw [this]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hy' _ (by omega)))
            (Ideal.pow_mem_of_mem _ hz' _ (by omega))
        exact (inferInstance : 𝔮.IsPrime).mem_of_pow_mem _ this
      · exact isRegularLocalRing_of_away k p 𝔮 hz' (rz_isRegularRing k p)
    · exact isRegularLocalRing_of_away k p 𝔮 hy' (ry_isRegularRing k p)

/-! ### The scheme-level singular locus -/

/-- The manuscript's `X`. -/
noncomputable abbrev hyperScheme : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (HyperRing k p))

/-- **`ex:charp-exceptional-fibre-paper`: the singular locus of `X` is `A = V(x,y,z)`.**
Exact set equality for the pointwise singular locus `stalkSingularLocus` of the actual scheme
`Spec k[x,y,z,t]/(x^p - t y^p - z^(p+1))`, in characteristic `p`, over any field `k`.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem hyper_stalkSingularLocus_eq [Fact p.Prime] [CharP k p] :
    Pcf.stalkSingularLocus (hyperScheme k p) =
      PrimeSpectrum.zeroLocus (center k p : Set (HyperRing k p)) := by
  rw [Pcf.stalkSingularLocus_Spec_eq]
  ext 𝔮
  simp only [Set.mem_compl_iff, Pcf.primeRegularLocus, Set.mem_ofPred_eq]
  rw [isRegularLocalRing_iff_not_mem k p 𝔮.asIdeal, not_not, center,
    PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_zeroLocus]
  simp [Set.insert_subset_iff]

/-! ### Codimension two -/

theorem center_isPrime (hp : 0 < p) : (center k p).IsPrime := by
  rw [← CharPExceptionalFibre.centerCoord_ker k p hp]
  exact RingHom.ker_isPrime _

theorem hx_mem_of (q : Ideal (HyperRing k p)) [q.IsPrime] (hp : 0 < p)
    (hyq : hy k p ∈ q) (hzq : hz k p ∈ q) : hx k p ∈ q := by
  have hrel := hyper_relation k p
  have : hx k p ^ p ∈ q := by
    have : hx k p ^ p = ht k p * hy k p ^ p + hz k p ^ (p + 1) := by
      linear_combination hrel
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hyq _ hp))
      (Ideal.pow_mem_of_mem _ hzq _ (by omega))
  exact (inferInstance : q.IsPrime).mem_of_pow_mem _ this

open scoped Classical in
/-- `A` is a minimal prime over `(y, z)`. -/
theorem center_mem_minimalPrimes (hp : 0 < p) :
    center k p ∈ (Ideal.span ((({hy k p, hz k p} : Finset (HyperRing k p)) :
      Set (HyperRing k p)))).minimalPrimes := by
  haveI := center_isPrime k p hp
  refine ⟨⟨inferInstance, ?_⟩, fun q ⟨hq, hle⟩ _ => ?_⟩
  · rw [Ideal.span_le, center]
    intro a ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact Ideal.subset_span (by simp)
  · have hy' : hy k p ∈ q := hle (Ideal.subset_span (by simp))
    have hz' : hz k p ∈ q := hle (Ideal.subset_span (by simp))
    rw [center, Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hx_mem_of k p q hp hy' hz'
    · exact hy'
    · exact hz'

open scoped Classical in
theorem center_height_le_two (hp : 0 < p) : (center k p).height ≤ 2 := by
  refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (center_mem_minimalPrimes k p hp)).trans ?_
  exact_mod_cast Finset.card_le_two

/-- A normal Noetherian local domain of dimension one is regular (it is a DVR). -/
theorem isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
    (L : Type*) [CommRing L] [IsLocalRing L] [IsDomain L] [IsNoetherianRing L]
    [IsIntegrallyClosed L] (hdim : ringKrullDim L = 1) : IsRegularLocalRing L := by
  have hnf : ¬ IsField L := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hdim
    exact zero_ne_one hdim
  have hmax : maximalIdeal L ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hnf
  have huniq : ∃! P : Ideal L, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal L, ⟨hmax, inferInstance⟩, fun P ⟨hP0, hP⟩ => ?_⟩
    have hle : P ≤ maximalIdeal L := le_maximalIdeal hP.ne_top
    by_contra hne
    have hlt : P < maximalIdeal L := lt_of_le_of_ne hle hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h0 : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h)
    have hm : (maximalIdeal L).height = 1 := by
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := L)
      rw [hdim] at this
      exact_mod_cast this
    rw [hm] at h1
    have : P.height = 0 := by
      have h1' : P.height + 1 ≤ 0 + 1 := by simpa using h1
      exact nonpos_iff_eq_zero.mp (WithTop.add_le_add_iff_right (by simp) |>.mp h1')
    exact h0 this
  haveI : IsDiscreteValuationRing L :=
    have h4 : IsIntegrallyClosed L ∧ ∃! P : Ideal L, P ≠ ⊥ ∧ P.IsPrime := ⟨inferInstance, huniq⟩
    ((IsDiscreteValuationRing.TFAE L hnf).out 1 4).mpr h4
  infer_instance

/-- **`A` has codimension two in `X`:** the height of the prime `(x,y,z)` is `2`.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem center_height_eq_two [Fact p.Prime] [CharP k p] : (center k p).height = 2 := by
  have hp := (Fact.out : p.Prime).pos
  haveI := center_isPrime k p hp
  haveI := hyperRing_isDomain k p hp
  haveI := hyperRing_isIntegrallyClosed k p
  refine le_antisymm (center_height_le_two k p hp) ?_
  by_contra hlt
  push Not at hlt
  have hne0 : (center k p).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    exact hy_ne_zero k p (by
      have : hy k p ∈ center k p := Ideal.subset_span (by simp)
      rw [h] at this
      exact this)
  have h1 : (center k p).height = 1 := by
    have : (center k p).height < 2 := hlt
    generalize (center k p).height = n at this hne0 ⊢
    induction n with
    | top => simp at this
    | coe n =>
      norm_cast at this hne0 ⊢
      omega
  let L := Localization.AtPrime (center k p)
  have hdim : ringKrullDim L = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (center k p) L, h1]
    rfl
  haveI : IsIntegrallyClosed L := isIntegrallyClosed_of_isLocalization L
    (center k p).primeCompl (center k p).primeCompl_le_nonZeroDivisors
  have hreg := isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one L hdim
  exact not_isRegularLocalRing_of_mem k p (center k p) (Fact.out : p.Prime).two_le
    (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) hreg

/-! ### The strict transform is smooth -/

/-- The strict-transform chart ring `k[y,u,v,t]/(u^p - t - y v^(p+1))` is `k`-isomorphic to
`k[y,u,v]`. -/
noncomputable def chartRingAlgEquiv :
    CharPExceptionalChart.ChartRing k p ≃ₐ[k] CharPExceptionalChart.ChartBase k :=
  AlgEquiv.ofRingEquiv (f := CharPExceptionalChart.chartRingEquiv k p) (fun c => by
    simp only [CharPExceptionalChart.chartRingEquiv, RingEquiv.trans_apply]
    change Polynomial.eval _ (Polynomial.C (MvPolynomial.C c)) = _
    rw [Polynomial.eval_C]
    rfl)

/-- **`ex:charp-exceptional-fibre-paper`: the strict transform `u^p - t - y v^(p+1) = 0` on
the `y`-chart is smooth over `k`.**

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem strictTransform_smooth : Algebra.Smooth k (CharPExceptionalChart.ChartRing k p) :=
  Algebra.Smooth.of_equiv (chartRingAlgEquiv k p).symm

/-- The `y`-chart of the actual blow-up, `Spec k[y,u,v]` (open in `Bl_A X` via
`yChartOpen`), is smooth over `k`. -/
theorem yChart_smooth : Algebra.Smooth k (CharPExceptionalChart.ChartBase k) := inferInstance

#print axioms hyperRing_isCohenMacaulayRing
#print axioms hyper_stalkSingularLocus_eq
#print axioms center_height_eq_two
#print axioms strictTransform_smooth

end Pcf.Examples.PaperP.CharPExceptionalSingular
