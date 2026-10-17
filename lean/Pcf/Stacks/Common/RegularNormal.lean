/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Pcf.Bounding.RegularLocalDomain
public import Pcf.Stacks.Common.RegularLocalization
public import Pcf.Stacks.Purity.NormalRing

/-!
# Regular rings are normal

This file proves Stacks Project Tag `0567`: a regular ring is normal.  Here a regular ring is
Mathlib's `IsRegularRing` (Noetherian, every localization at a prime is a regular local ring),
which is the Stacks definition (Tag `00OD`), and normal is pcf's `IsStacksNormalRing`, the
Stacks definition (Tag `00GV`, Definition 10.37.11).

## Route

Stacks proves `0567` via Serre's criterion `(R₁) + (S₂)` (Tag `031S`).  We use a shorter route
that avoids Serre's criterion and the Ext-theoretic depth API.

1. A regular local ring `A` with `dim A ≥ 2` has `x, y ∈ 𝔪` with `x ≠ 0` and `y` a
   nonzerodivisor on `A ⧸ (x)`: take `x ∈ 𝔪 \ 𝔪²`; then `A ⧸ (x)` is regular local of
   positive dimension (pcf), hence a domain (Tag `00NP`) with a nonzero maximal ideal.
2. Consequently, for `b ≠ 0`, the maximal ideal of such an `A` is not an associated prime of
   `A ⧸ (b)` (this is the depth-two input used in the `(S₂)` part of the Stacks proof).
3. If `R` is a regular Noetherian domain and `a / b` lies in `R_𝔭` for every prime `𝔭` with
   `R_𝔭` integrally closed, then `a ∈ (b)`: otherwise an associated prime `𝔭` of `R ⧸ (b)`
   containing `((b) : a)` has `R_𝔭` regular local of dimension exactly one (by 2), hence a DVR
   (Tag `00PD`), so `a / b ∈ R_𝔭` gives a contradiction.  Mathlib's
   `IsIntegrallyClosed.of_localization` then shows `R` is integrally closed.

The local statement for a regular *local* ring `R` needs `IsRegularRing R`, which is Stacks Tag
`0AFS` (localizations of a regular local ring are regular), proved in
`Pcf.Stacks.Common.RegularLocalization` from the vendored mathlib4 PR #29802.
-/

@[expose] public section

noncomputable section

universe u

namespace Pcf.Stacks

open IsLocalRing

section Pair

variable {A : Type*} [CommRing A]

/-- Elementary depth-two cancellation: if `x, y` is a regular sequence in a domain and
`x c, y c ∈ (b)` with `b ≠ 0`, then `c ∈ (b)`. -/
theorem mem_span_singleton_of_regular_pair [IsDomain A] {x y b c : A} (hx : x ≠ 0)
    (hb : b ≠ 0) (hreg : ∀ u, y * u ∈ Ideal.span {x} → u ∈ Ideal.span {x})
    (hxc : x * c ∈ Ideal.span {b}) (hyc : y * c ∈ Ideal.span {b}) :
    c ∈ Ideal.span {b} := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hxc
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hyc
  have hyu : y * u = v * x := by
    apply mul_left_cancel₀ hb
    linear_combination y * hu - x * hv
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp
    (hreg u (Ideal.mem_span_singleton'.mpr ⟨v, hyu.symm⟩))
  refine Ideal.mem_span_singleton'.mpr ⟨w, ?_⟩
  apply mul_left_cancel₀ hx
  linear_combination b * hw + hu

/-- A regular local ring of dimension at least two contains a regular sequence `x, y` of length
two in its maximal ideal.  This is the length-two case of the regular-sequence statement of
Stacks Tag `00NQ` (whose minimal generators need not be the ones chosen here), as needed for the
`(S₂)` part of Tag `0567`; it is not tagged since it is only a consequence of that tag. -/
theorem exists_regular_pair_of_two_le_ringKrullDim [IsRegularLocalRing A]
    (hdim : 2 ≤ ringKrullDim A) :
    ∃ x y : A, x ∈ maximalIdeal A ∧ y ∈ maximalIdeal A ∧ x ≠ 0 ∧
      ∀ u, y * u ∈ Ideal.span {x} → u ∈ Ideal.span {x} := by
  set n := (maximalIdeal A).spanFinrank with hn
  have hnA : ringKrullDim A = n := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have hn2 : 2 ≤ n := by
    rw [hnA] at hdim
    exact_mod_cast hdim
  -- a minimal generator `x ∈ 𝔪 \ 𝔪²`
  have hcot : Module.finrank (ResidueField A) (CotangentSpace A) = n := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
    rw [hnA] at h
    exact_mod_cast h
  have : Nontrivial (CotangentSpace A) :=
    Module.nontrivial_of_finrank_pos (R := ResidueField A) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : CotangentSpace A)
  obtain ⟨⟨x, hxm⟩, rfl⟩ := (maximalIdeal A).toCotangent_surjective v
  have hx2 : x ∉ maximalIdeal A ^ 2 := fun h =>
    hv ((Ideal.toCotangent_eq_zero _ _).mpr h)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (Ideal.zero_mem _)
  have hspan_le : Ideal.span {x} ≤ maximalIdeal A :=
    (Ideal.span_singleton_le_iff_mem _).mpr hxm
  have : Nontrivial (A ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      hspan_le)
  let B := A ⧸ Ideal.span {x}
  let _ : IsRegularLocalRing B := isRegularLocalRing_quotient_minimalGenerator hxm hx2
  have hdimB : ringKrullDim B = (n - 1 : ℕ) :=
    ringKrullDim_quotient_minimalGenerator_eq hxm hx2 (n - 1)
      (by rw [hnA]; norm_cast; omega)
  let _ : IsDomain B := Pcf.Vendor.isDomain_of_isRegularLocalRing B
  have hmB : maximalIdeal B ≠ ⊥ := by
    intro h
    have hfield : IsField B := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
    have h0 := ringKrullDim_eq_zero_of_isField hfield
    rw [hdimB] at h0
    have : n - 1 = 0 := by exact_mod_cast h0
    omega
  obtain ⟨yb, hybm, hyb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmB
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  refine ⟨x, y, hxm, ?_, hx0, ?_⟩
  · by_contra hy
    have hunit : IsUnit y := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hy
    exact (IsLocalRing.mem_maximalIdeal _).mp hybm (hunit.map _)
  · intro u hu
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hu ⊢
    rw [map_mul] at hu
    exact (mul_eq_zero.mp hu).resolve_left hyb0

/-- In a regular local ring of dimension at least two, the maximal ideal is not an associated
prime of `A ⧸ (b)` for `b ≠ 0`: if `𝔪 c ⊆ (b)` then `c ∈ (b)`.  This is the depth-two
statement behind the `(S₂)` part of Stacks Tag `0567`. -/
theorem mem_span_singleton_of_maximalIdeal_mul_le [IsRegularLocalRing A]
    (hdim : 2 ≤ ringKrullDim A) {b c : A} (hb : b ≠ 0)
    (hc : ∀ z ∈ maximalIdeal A, z * c ∈ Ideal.span {b}) : c ∈ Ideal.span {b} := by
  let _ : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  obtain ⟨x, y, hx, hy, hx0, hreg⟩ := exists_regular_pair_of_two_le_ringKrullDim hdim
  exact mem_span_singleton_of_regular_pair hx0 hb hreg (hc x hx) (hc y hy)

end Pair

section Domain

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularRing R]

omit [IsDomain R] [IsRegularRing R] in
/-- Smul in `R ⧸ I` as an `R`-module, in the form used for colon ideals. -/
private theorem smul_mk_eq_zero_iff (I : Ideal R) (r c : R) :
    r • Ideal.Quotient.mk I c = 0 ↔ r * c ∈ I := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]

/-- An associated prime `𝔭` of `R ⧸ (b)`, `b ≠ 0`, in a regular domain has `R_𝔭` integrally
closed: `R_𝔭` is regular local of dimension one, hence a DVR. -/
private theorem isIntegrallyClosed_atPrime_of_colon {b c : R} (hb : b ≠ 0) (P : Ideal R)
    [hP : P.IsPrime] (hPb : b ∈ P) (hPc : ∀ r, r ∈ P ↔ r * c ∈ Ideal.span {b}) :
    IsIntegrallyClosed (Localization.AtPrime P) := by
  let A := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  let _ : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  -- `dim A ≠ 0`, since `P ≠ ⊥`
  have hP0 : P.height ≠ 0 := by
    intro h
    rw [Ideal.height_eq_zero_iff] at h
    have hle : P ≤ ⊥ := h.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    exact hb ((Submodule.eq_bot_iff P).mp (le_bot_iff.mp hle) b hPb)
  -- `dim A < 2`, by the depth-two statement
  have hlt2 : ¬ 2 ≤ ringKrullDim A := by
    intro h2
    have hmem : algebraMap R A c ∈ Ideal.span {algebraMap R A b} := by
      apply mem_span_singleton_of_maximalIdeal_mul_le h2
        (fun h0 => hb (hinj (by rw [h0, map_zero])))
      intro z hz
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl (S := A) z
      rw [IsLocalization.AtPrime.mk'_mem_maximal_iff A P] at hz
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp ((hPc r).mp hz)
      refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' A e s, ?_⟩
      apply (IsLocalization.map_units A s).mul_right_cancel
      rw [mul_right_comm, IsLocalization.mk'_spec, mul_right_comm, IsLocalization.mk'_spec,
        ← map_mul, ← map_mul, he]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨⟨e, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl (S := A) w
    have hes : algebraMap R A (e * b) = algebraMap R A (c * s) := by
      rw [map_mul, map_mul, ← hw, mul_right_comm, IsLocalization.mk'_spec]
    have hsc : (s : R) * c ∈ Ideal.span {b} :=
      Ideal.mem_span_singleton'.mpr ⟨e, by rw [hinj hes, mul_comm]⟩
    exact s.2 ((hPc s).mpr hsc)
  have hdimA : ringKrullDim A = P.height := IsLocalization.AtPrime.ringKrullDim_eq_height P A
  have hnA : ringKrullDim A = ((maximalIdeal A).spanFinrank : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have hone : ringKrullDim A = 1 := by
    have h1 : (maximalIdeal A).spanFinrank ≠ 0 := by
      intro h
      rw [h, hdimA] at hnA
      exact hP0 (by exact_mod_cast hnA)
    have h2 : ¬ 2 ≤ (maximalIdeal A).spanFinrank := by
      intro h
      exact hlt2 (by rw [hnA]; exact_mod_cast h)
    rw [hnA]
    have : (maximalIdeal A).spanFinrank = 1 := by omega
    rw [this]
    rfl
  let _ : IsDiscreteValuationRing A :=
    Pcf.Vendor.IsDiscreteValuationRing.of_isRegularLocalRing_of_ringKrullDim_eq_one A hone
  infer_instance

/-- **Stacks Project Tag 0567, domain case.** A regular Noetherian domain is integrally closed.

Proof route differs from Stacks (which uses Serre's criterion `031S`): an element `a / b` of the
fraction field lying in `R_𝔭` for every `𝔭` with `R_𝔭` integrally closed lies in `R`, because an
associated prime of `R ⧸ (b)` containing `((b) : a)` has height one (depth-two argument); then
Mathlib's `IsIntegrallyClosed.of_localization` applies. -/
@[stacks 0567 "domain case, in the form `IsIntegrallyClosed`"]
theorem isIntegrallyClosed_of_isRegularRing : IsIntegrallyClosed R := by
  classical
  let K := FractionRing R
  apply IsIntegrallyClosed.of_localization
    {p : PrimeSpectrum R | IsIntegrallyClosed (Localization.AtPrime p.asIdeal)} (fun _ hp => hp)
  rw [eq_bot_iff]
  intro z hz
  simp only [Algebra.mem_iInf] at hz
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) (K := K) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  by_cases hab : a ∈ Ideal.span {b}
  · obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hab
    rw [Algebra.mem_bot]
    exact ⟨r, by rw [← hr, map_mul, mul_div_cancel_right₀ _ hbK]⟩
  exfalso
  have hne : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hne
  obtain ⟨hPprime, y, hPy⟩ := (isAssociatedPrime_iff).mp hPass
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hPc : ∀ r, r ∈ P ↔ r * c ∈ Ideal.span {b} := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff]
  have hcolon : ∀ r, r * a ∈ Ideal.span {b} → r ∈ P := by
    intro r hr
    apply hle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff]
    exact hr
  have hPb : b ∈ P := hcolon b (Ideal.mem_span_singleton'.mpr ⟨a, mul_comm _ _⟩)
  have hint := isIntegrallyClosed_atPrime_of_colon R hb0 P hPb hPc
  have hzP := hz ⟨P, hPprime⟩ hint
  have hzP' : algebraMap R K a / algebraMap R K b ∈
      Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors := by
    rw [Localization.subalgebra.ofField_eq]
    exact hzP
  obtain ⟨r, s, hs, hrs⟩ := hzP'
  have hsK : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (P.primeCompl_le_nonZeroDivisors hs)
  have hK : algebraMap R K (s * a) = algebraMap R K (r * b) := by
    rw [map_mul, map_mul]
    have hrs' := hrs
    rw [div_eq_iff hbK] at hrs'
    rw [hrs']
    have hss : algebraMap R K s * (algebraMap R K s)⁻¹ = 1 := mul_inv_cancel₀ hsK
    linear_combination (algebraMap R K r * algebraMap R K b) * hss
  have hsa : s * a ∈ Ideal.span {b} :=
    Ideal.mem_span_singleton'.mpr ⟨r, (IsFractionRing.injective R K hK).symm⟩
  exact hs (hcolon s hsa)

end Domain

section Regular

/-- A localization of a regular ring at a prime is again a regular ring: its own localizations at
primes are localizations of the original ring at primes. -/
theorem isRegularRing_localization_atPrime (R : Type*) [CommRing R] [IsRegularRing R]
    (p : Ideal R) [p.IsPrime] : IsRegularRing (Localization.AtPrime p) := by
  rw [isRegularRing_iff]
  intro q _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization p.primeCompl q).toRingEquiv

/-- **Stacks Project Tag 0567.** A regular ring is normal.

Here "regular" is Mathlib's `IsRegularRing` (Stacks Tag `00OD`) and "normal" is
`IsStacksNormalRing` (Stacks Tag `00GV`), so the statement is exactly the tag.  The proof route
differs from Stacks: see `isIntegrallyClosed_of_isRegularRing`. -/
@[stacks 0567]
theorem isStacksNormalRing_of_isRegularRing (R : Type u) [CommRing R] [IsRegularRing R] :
    IsStacksNormalRing R := by
  intro p
  let A := Localization.AtPrime p.asIdeal
  let _ : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  let _ : IsRegularRing A := isRegularRing_localization_atPrime R p.asIdeal
  exact ⟨inferInstance, isIntegrallyClosed_of_isRegularRing A⟩

/-- **Stacks Project Tag 0567, regular local case.** A regular local ring is integrally closed.

Tag `0567` is stated for regular rings (Tag `00OD`); a regular local ring is a regular ring by
Tag `0AFS` (`Pcf.Vendor.isRegularRing_of_isRegularLocalRing`).

The proof route differs from Stacks (which uses Serre's criterion `031S`); see
`isIntegrallyClosed_of_isRegularRing`. -/
@[stacks 0567 "regular local case"]
theorem isIntegrallyClosed_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsIntegrallyClosed R := by
  let _ : IsRegularRing R := Pcf.Vendor.isRegularRing_of_isRegularLocalRing R
  let _ : IsDomain R := Pcf.Vendor.isDomain_of_isRegularLocalRing R
  exact isIntegrallyClosed_of_isRegularRing R

/-- **Stacks Project Tag 0567, regular local case**, in the Stacks normal-ring form.

The proof route differs from Stacks (which uses Serre's criterion `031S`); see
`isIntegrallyClosed_of_isRegularRing`. -/
@[stacks 0567 "regular local case"]
theorem isStacksNormalRing_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : IsStacksNormalRing R := by
  let _ : IsRegularRing R := Pcf.Vendor.isRegularRing_of_isRegularLocalRing R
  exact isStacksNormalRing_of_isRegularRing R

end Regular

end Pcf.Stacks
