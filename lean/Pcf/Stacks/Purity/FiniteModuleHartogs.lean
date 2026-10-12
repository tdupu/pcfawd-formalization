/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Pcf.Stacks.Purity.DepthTwo
import Pcf.Stacks.Purity.NormalRing

/-!
# The module-theoretic Hartogs intersection

The algebraic core of recovery across a punctured spectrum works for modules.  If `x` is regular
on `M` and `y` is regular on `M / xM`, then two elements of `M` which become equal after allowing
powers of `x` and `y` already arise from one element of `M`.

This formulation will be applied to a finite normal algebra viewed as a module over its local
base.  It deliberately contains no normality or scheme-theoretic hypotheses.
-/

noncomputable section
set_option linter.style.haveILetI false

open scoped Pointwise

universe u v

namespace Pcf.Stacks

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Divisibility by a power of the first member of a module-regular pair can be cancelled across
a power of the second member. -/
theorem exists_eq_pow_smul_of_regular_pair
    {x y : R} {a b : M} (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y)
    (m n : ℕ) (h : y ^ m • a = x ^ n • b) :
    ∃ c : M, a = x ^ n • c := by
  induction n generalizing a b with
  | zero => exact ⟨a, by simp⟩
  | succ n ih =>
      have hmem : y ^ m • a ∈ x • (⊤ : Submodule R M) := by
        refine ⟨x ^ n • b, Submodule.mem_top, ?_⟩
        change x • (x ^ n • b) = y ^ m • a
        simpa only [pow_succ', mul_smul] using h.symm
      have ha : a ∈ x • (⊤ : Submodule R M) :=
        mem_of_isSMulRegular_quotient_of_smul_mem (hy.pow m) hmem
      obtain ⟨a', -, rfl⟩ := ha
      have h' : y ^ m • a' = x ^ n • b := by
        apply hx
        change y ^ m • (x • a') = x ^ (n + 1) • b at h
        simpa only [smul_smul, pow_succ', mul_comm, mul_left_comm, mul_assoc] using h
      obtain ⟨c, hc⟩ := ih h'
      refine ⟨c, ?_⟩
      change x • a' = x ^ (n + 1) • c
      rw [hc, pow_succ', mul_smul]

/-- Two module fractions with denominators supported on a module-regular pair have a common value
in the original module.  The displayed equalities say that `a / x^n` and `b / y^m` are both the
image of `c`. -/
theorem exists_common_value_of_module_regular_pair
    {x y : R} {a b : M} (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y)
    (m n : ℕ) (h : y ^ m • a = x ^ n • b) :
    ∃ c : M, a = x ^ n • c ∧ b = y ^ m • c := by
  obtain ⟨c, hc⟩ := exists_eq_pow_smul_of_regular_pair hx hy m n h
  refine ⟨c, hc, ?_⟩
  apply hx.pow n
  change x ^ n • b = x ^ n • (y ^ m • c)
  rw [← h, hc]
  simp only [smul_smul]
  ac_rfl

open IsLocalRing Module

variable {B : Type v} [CommRing B] [Algebra R B]

/-- A minimal prime of a Noetherian algebra which is torsion-free over a domain contracts to
zero.  The point is that minimal primes are associated, whereas every nonzero base scalar acts
regularly on the algebra. -/
theorem minimalPrime_under_eq_bot_of_isTorsionFree
    [IsDomain R] [Module.IsTorsionFree R B] [IsNoetherianRing B]
    (p : Ideal B) (hp : p ∈ minimalPrimes B) :
    p.under R = ⊥ := by
  have hpAss : p ∈ associatedPrimes B B := by
    apply associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B
    have hann : annihilator B B = ⊥ := by
      ext b
      constructor
      · intro hb
        simpa using (Module.mem_annihilator.mp hb 1)
      · intro hb
        have : b = 0 := by simpa using hb
        subst b
        exact Submodule.zero_mem _
    rwa [hann]
  apply le_antisymm ?_ bot_le
  intro r hr
  by_contra hr0
  have hrreg : IsSMulRegular B r :=
    IsTorsionFree.isSMulRegular (show IsRegular r from isRegular_iff_ne_zero.mpr hr0)
  have hrregB : IsSMulRegular B (algebraMap R B r) := by
    intro a b hab
    apply hrreg
    change algebraMap R B r * a = algebraMap R B r * b at hab
    simpa only [Algebra.smul_def] using hab
  have hmemUnion : algebraMap R B r ∈ ⋃ q ∈ associatedPrimes B B, (q : Set B) :=
    Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hpAss hr)
  rw [biUnion_associatedPrimes_eq_compl_regular B B] at hmemUnion
  exact hmemUnion hrregB

/-- For a finite torsion-free algebra over a normal local domain, every prime above the closed
point has height at least that of the closed point.  We pass to a minimal domain component and use
going down there, then compare heights along the quotient map. -/
theorem two_le_height_of_liesOver_of_finite_torsionFree
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Module.IsTorsionFree R B] [IsNoetherianRing B] [Module.Finite R B]
    (q : Ideal B) [q.IsPrime] (hq : q.under R = maximalIdeal R)
    (hdim : 2 ≤ ringKrullDim R) :
    2 ≤ q.height := by
  obtain ⟨p, hpmin, hpq⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := q) bot_le
  let C := B ⧸ p
  letI : p.IsPrime := hpmin.isPrime
  letI : CommRing C := inferInstance
  letI : Algebra R C := inferInstance
  letI : IsDomain C := inferInstance
  have hpunder : p.under R = ⊥ :=
    minimalPrime_under_eq_bot_of_isTorsionFree p hpmin
  have hmapinj : Function.Injective (algebraMap R C) := by
    intro a b hab
    apply sub_eq_zero.mp
    have habp : algebraMap R B (a - b) ∈ p := by
      rw [map_sub, ← Ideal.Quotient.eq]
      simpa [C] using hab
    have : a - b ∈ p.under R := habp
    rw [hpunder] at this
    simpa using this
  letI : Module.IsTorsionFree R C :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hmapinj
  let Q : Ideal C := q.map (Ideal.Quotient.mk p)
  letI : Q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have hQunderB : Q.under B = q := Ideal.comap_map_mk hpq
  have hQunder : Q.under R = maximalIdeal R := by
    rw [← hq, ← hQunderB]
    exact Ideal.under_under Q
  letI : Q.LiesOver (maximalIdeal R) := ⟨hQunder.symm⟩
  have hmheight : (maximalIdeal R).height ≤ Q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) Q]
    exact le_add_right le_rfl
  have hQq : Q.height ≤ q.height := by
    have hheight := Order.height_le_height_apply_of_strictMono
      (PrimeSpectrum.comap (Ideal.Quotient.mk p))
      (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
      (⟨Q, inferInstance⟩ : PrimeSpectrum C)
    rw [← PrimeSpectrum.height_eq_orderHeight,
      ← PrimeSpectrum.height_eq_orderHeight] at hheight
    change Q.height ≤ (Q.under B).height at hheight
    rwa [hQunderB] at hheight
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hdim
  have hdim' : (2 : ℕ∞) ≤ (maximalIdeal R).height :=
    WithBot.coe_le_coe.mp hdim
  exact hdim'.trans (hmheight.trans hQq)

omit [Module R M] [AddCommGroup M] in
/-- An associated closed point of `B / xB` over the base produces a `B`-associated prime above
the closed point.  This is the bridge from base-module associated primes to localization on the
normal algebra. -/
theorem exists_associatedPrime_liesOver_closedPoint
    [IsLocalRing R] [IsNoetherianRing R] [IsNoetherianRing B]
    (x : R)
    (hAss : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x B)) :
    ∃ q : Ideal B,
      q ∈ associatedPrimes B (B ⧸ Ideal.span ({algebraMap R B x} : Set B)) ∧
      q.under R = maximalIdeal R := by
  obtain ⟨-, a0, ha0⟩ := isAssociatedPrime_iff.mp hAss
  obtain ⟨a, rfl⟩ := (x • (⊤ : Submodule R B)).mkQ_surjective a0
  let I : Ideal B := Ideal.span ({algebraMap R B x} : Set B)
  let aI : B ⧸ I := Ideal.Quotient.mk I a
  have haquot_ne : (Submodule.Quotient.mk a : QuotSMulTop x B) ≠ 0 := by
    intro haquot
    have htop : (⊥ : Submodule R (QuotSMulTop x B)).colon
        {(Submodule.Quotient.mk a : QuotSMulTop x B)} = ⊤ := by
      rw [haquot, Submodule.colon_singleton_zero]
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (ha0.trans htop)
  have haI_ne : aI ≠ 0 := by
    intro haI
    apply haquot_ne
    rw [Submodule.Quotient.mk_eq_zero]
    have ha_mem_I : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp haI
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha_mem_I
    refine ⟨b, Submodule.mem_top, ?_⟩
    change x • b = a
    simpa only [Algebra.smul_def, mul_comm] using hb
  obtain ⟨q, hqAss, hcolon⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing B aI haI_ne
  refine ⟨q, hqAss, ?_⟩
  apply le_antisymm
  · have : (q.under R).IsPrime := hqAss.isPrime.comap (algebraMap R B)
    exact IsLocalRing.le_maximalIdeal this.ne_top'
  · intro r hr
    have hrcolon : r ∈ (⊥ : Submodule R (QuotSMulTop x B)).colon
        {(Submodule.Quotient.mk a : QuotSMulTop x B)} := ha0 ▸ hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hrcolon
    have hra : r • a ∈ x • (⊤ : Submodule R B) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      simpa only [Submodule.Quotient.mk_smul] using hrcolon
    have hraI : algebraMap R B r * a ∈ I := by
      obtain ⟨b, -, hb⟩ := hra
      have : r • a ∈ I := by
        rw [← hb]
        simpa only [DistribSMul.toLinearMap_apply, Algebra.smul_def] using
          Ideal.mul_mem_right b I (Ideal.subset_span (Set.mem_singleton _))
      simpa only [Algebra.smul_def] using this
    have hrann : algebraMap R B r ∈
        (⊥ : Submodule B (B ⧸ I)).colon {aI} := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      change Ideal.Quotient.mk I (algebraMap R B r * a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hraI
    exact hcolon hrann

omit [Module R M] [AddCommGroup M] in
/-- Localizing a principal ideal gives the submodule generated by the image of its generator. -/
theorem localized_span_singleton_eq_smul_top (q : Ideal B) [q.IsPrime] (z : B) :
    (Ideal.span ({z} : Set B) : Submodule B B).localized q.primeCompl =
      algebraMap B (Localization.AtPrime q) z •
        (⊤ : Submodule (Localization.AtPrime q) (Localization.AtPrime q)) := by
  change (Ideal.span ({z} : Set B) : Submodule B B).localized'
      (Localization.AtPrime q) q.primeCompl
        (LocalizedModule.mkLinearMap q.primeCompl B) = _
  rw [Submodule.localized'_span, Set.image_singleton]
  change Submodule.span (Localization.AtPrime q)
      ({algebraMap B (Localization.AtPrime q) z} : Set (Localization.AtPrime q)) = _
  rw [Ideal.submodule_span_eq, ← Submodule.set_smul_top_eq_span,
    Submodule.singleton_set_smul]

/-- A finite torsion-free Stacks-normal algebra has no closed-point associated prime after
quotienting by a nonzero element of the base maximal ideal.  The contradiction is checked after
localizing at an associated prime, where Stacks-normality supplies a normal domain of dimension at
least two. -/
theorem principalQuotient_avoid_closedPoint_of_finite_stacksNormal
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Module.IsTorsionFree R B] [Module.Finite R B]
    (hB : IsStacksNormalRing B) (hdim : 2 ≤ ringKrullDim R)
    (x : R) (hxm : x ∈ maximalIdeal R) (hx : x ≠ 0) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x B) := by
  intro hAss
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let I : Ideal B := Ideal.span ({algebraMap R B x} : Set B)
  obtain ⟨q, hqAss0, hqunder⟩ :=
    exists_associatedPrime_liesOver_closedPoint x hAss
  have hqAss : q ∈ associatedPrimes B (B ⧸ I) := by
    simpa [I] using hqAss0
  letI : q.IsPrime := hqAss.isPrime
  let Bq := Localization.AtPrime q
  letI : IsDomain Bq := hB.isDomain_atPrime ⟨q, inferInstance⟩
  letI : IsIntegrallyClosed Bq := hB.isIntegrallyClosed_atPrime ⟨q, inferInstance⟩
  have hqheight : 2 ≤ q.height :=
    two_le_height_of_liesOver_of_finite_torsionFree q hqunder hdim
  have hdimq : 2 ≤ ringKrullDim Bq := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q Bq]
    exact WithBot.coe_le_coe.mpr hqheight
  let z : Bq := algebraMap B Bq (algebraMap R B x)
  have hz : z ≠ 0 := by
    intro hz0
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff q.primeCompl Bq (algebraMap R B x)).mp hz0
    have hxreg : IsSMulRegular B x :=
      IsTorsionFree.isSMulRegular (show IsRegular x from isRegular_iff_ne_zero.mpr hx)
    have hs0 : (s : B) = 0 := by
      apply hxreg
      change x • (s : B) = x • (0 : B)
      simpa only [Algebra.smul_def, smul_zero, mul_comm, zero_mul] using hs
    exact s.property (hs0 ▸ q.zero_mem)
  have hzmax : z ∈ maximalIdeal Bq := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff Bq q]
    change x ∈ q.under R
    rwa [hqunder]
  have hloc : maximalIdeal Bq ∈
      associatedPrimes Bq (LocalizedModule q.primeCompl (B ⧸ I)) :=
    associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hqAss
  have hIloc : (I : Submodule B B).localized q.primeCompl =
      z • (⊤ : Submodule Bq Bq) := by
    simpa [I, z, Bq] using localized_span_singleton_eq_smul_top q (algebraMap R B x)
  let e0 : QuotSMulTop z Bq ≃ₗ[Bq]
      (LocalizedModule q.primeCompl B ⧸ (I : Submodule B B).localized q.primeCompl) :=
    Submodule.quotEquivOfEq _ _ hIloc.symm
  let e : QuotSMulTop z Bq ≃ₗ[Bq]
      LocalizedModule q.primeCompl (B ⧸ I) :=
    e0 ≪≫ₗ localizedQuotientEquiv q.primeCompl (I : Submodule B B)
  have hloc' : maximalIdeal Bq ∈ associatedPrimes Bq (QuotSMulTop z Bq) :=
    e.isAssociatedPrime_iff.mpr hloc
  exact (principalQuotientsAvoidClosedPoint_of_two_le_ringKrullDim Bq hdimq)
    z hzmax hz hloc'

/-- Finite prime avoidance for an arbitrary finite module: if the closed point is not associated
to `M / xM`, some element of the maximal ideal acts regularly on that quotient. -/
theorem exists_isSMulRegular_quotient_mem_maximalIdeal_of_finite
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    (x : R)
    (hAss : maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x M)) :
    ∃ y ∈ maximalIdeal R, IsSMulRegular (QuotSMulTop x M) y := by
  by_contra h
  push Not at h
  have hsubset : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ p ∈ associatedPrimes R (QuotSMulTop x M), (p : Set R) := by
    intro y hym
    rw [biUnion_associatedPrimes_eq_compl_regular R (QuotSMulTop x M)]
    simpa using h y hym
  obtain ⟨p, hpAss, hmp⟩ :=
    ((maximalIdeal R).subset_union_prime_finite
      (associatedPrimes.finite R (QuotSMulTop x M)) (f := id) 0 0
      (fun _ hp _ _ ↦ hp.isPrime)).mp hsubset
  have hp_le : p ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hpAss.isPrime.ne_top'
  have hp : p = maximalIdeal R := le_antisymm hp_le hmp
  exact hAss (hp ▸ hpAss)

/-- Over a Noetherian local ring, the second member of a finite-module regular pair is regular on
the module itself.  The kernel of multiplication by `y` is contained in `x` times itself, so
Nakayama's lemma kills it. -/
theorem isSMulRegular_of_isSMulRegular_quotient_of_finite
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    {x y : R} (hxm : x ∈ maximalIdeal R) (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y) :
    IsSMulRegular M y := by
  rw [isSMulRegular_iff_ker_lsmul_eq_bot]
  let N := LinearMap.ker (LinearMap.lsmul R M y)
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (Ideal.span {x}) N (IsNoetherian.noetherian _)
  · rw [Submodule.ideal_span_singleton_smul]
    intro b hb
    have hyb : y • b = 0 := LinearMap.mem_ker.mp hb
    have hb_x : b ∈ x • (⊤ : Submodule R M) :=
      mem_of_isSMulRegular_quotient_of_smul_mem hy (hyb ▸ Submodule.zero_mem _)
    obtain ⟨c, -, hc⟩ := hb_x
    change x • c = b at hc
    refine ⟨c, ?_, hc⟩
    apply LinearMap.mem_ker.mpr
    apply hx
    change x • (y • c) = x • (0 : M)
    rw [smul_comm, hc, hyb, smul_zero]
  · exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxm)).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)

/-- A finite torsion-free Stacks-normal algebra over a normal Noetherian local domain of dimension
at least two admits a base regular pair.  This is the exact module-depth input for Hartogs recovery
of the algebra. -/
theorem exists_module_regular_pair_of_finite_stacksNormal
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Module.IsTorsionFree R B] [Module.Finite R B]
    (hB : IsStacksNormalRing B) (hdim : 2 ≤ ringKrullDim R) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧
      IsSMulRegular B x ∧ IsSMulRegular (QuotSMulTop x B) y := by
  have hdim1 : 1 ≤ ringKrullDim R := (by norm_num : (1 : WithBot ℕ∞) ≤ 2).trans hdim
  obtain ⟨x, hxm, hx⟩ := exists_nonzero_mem_maximalIdeal_of_one_le_ringKrullDim R hdim1
  have hAss := principalQuotient_avoid_closedPoint_of_finite_stacksNormal hB hdim x hxm hx
  obtain ⟨y, hym, hy⟩ :=
    exists_isSMulRegular_quotient_mem_maximalIdeal_of_finite x hAss
  have hxreg : IsSMulRegular B x :=
    IsTorsionFree.isSMulRegular (show IsRegular x from isRegular_iff_ne_zero.mpr hx)
  exact ⟨x, y, hxm, hym, hxreg, hy⟩

/-- The same regular pair can be chosen so that each member is regular on the finite algebra,
while the second remains regular modulo the first. -/
theorem exists_module_permutable_regular_pair_of_finite_stacksNormal
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Module.IsTorsionFree R B] [Module.Finite R B]
    (hB : IsStacksNormalRing B) (hdim : 2 ≤ ringKrullDim R) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧
      IsSMulRegular B x ∧ IsSMulRegular B y ∧
        IsSMulRegular (QuotSMulTop x B) y := by
  obtain ⟨x, y, hxm, hym, hx, hy⟩ :=
    exists_module_regular_pair_of_finite_stacksNormal hB hdim
  exact ⟨x, y, hxm, hym, hx,
    isSMulRegular_of_isSMulRegular_quotient_of_finite hxm hx hy, hy⟩

end Pcf.Stacks
