/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FiniteFreeRegularDescent
public import Pcf.Bounding.SingularLocusClosedOfGenericRegularity

/-!
# Descending generic regularity along a finite radicial extension

Let `A ⊆ B` be a finite extension of Noetherian domains such that some fixed
power of every element of `B` lies in `A` (a purely inseparable, "radicial"
extension). If `B` is regular on a nonempty basic open set, so is `A`. The
proof combines generic freeness, uniqueness of primes over a prime of `A`, and
descent of regularity along finite free local extensions.
-/

@[expose] public section

namespace Pcf

open IsLocalRing

universe u

set_option linter.style.haveILetI false

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- In a radicial extension, a prime of `A` has at most one prime of `B` over it. -/
theorem eq_of_comap_eq_of_pow_mem {n : ℕ} (hn : 0 < n)
    (hpow : ∀ b : B, b ^ n ∈ Set.range (algebraMap A B)) {Q₁ Q₂ : Ideal B}
    [Q₁.IsPrime] [Q₂.IsPrime] (h : Q₁.comap (algebraMap A B) = Q₂.comap (algebraMap A B)) :
    Q₁ = Q₂ := by
  have key : ∀ (P₁ P₂ : Ideal B) [P₁.IsPrime] [P₂.IsPrime],
      P₁.comap (algebraMap A B) = P₂.comap (algebraMap A B) → P₁ ≤ P₂ := by
    intro P₁ P₂ _ _ hP b hb
    obtain ⟨a, ha⟩ := hpow b
    have : a ∈ P₁.comap (algebraMap A B) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.pow_mem_of_mem P₁ hb n hn
    rw [hP, Ideal.mem_comap, ha] at this
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n this
  exact le_antisymm (key Q₁ Q₂ h) (key Q₂ Q₁ h.symm)

/-- A maximal ideal of `B_p` contracts to `p` when `B` is finite over `A`. -/
theorem comap_comap_maximal_localization [Module.Finite A B] (p : Ideal A) [p.IsPrime]
    (M : Ideal (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) [M.IsMaximal] :
    (M.comap (algebraMap B _)).comap (algebraMap A B) = p := by
  set Bp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  set Ap := Localization.AtPrime p
  have : Algebra.IsIntegral Ap Bp := Algebra.IsIntegral.of_finite Ap Bp
  have hmax : (M.comap (algebraMap Ap Bp)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (Algebra.IsIntegral.isIntegral) M
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq A Ap Bp, ← Ideal.comap_comap,
    IsLocalRing.eq_maximalIdeal hmax]
  exact Localization.AtPrime.under_maximalIdeal

/-- Localizing a finite radicial extension of domains at a prime of the base gives a
local ring. -/
theorem isLocalRing_localization_of_pow_mem [IsDomain B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ b : B, b ^ n ∈ Set.range (algebraMap A B)) (p : Ideal A) [p.IsPrime] :
    IsLocalRing (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) := by
  set S := Algebra.algebraMapSubmonoid B p.primeCompl
  set Bp := Localization S
  have hS : S ≤ nonZeroDivisors B := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ha ?_
    rw [(map_eq_zero_iff _ hinj).mp h0]
    exact p.zero_mem
  have : Nontrivial Bp := (IsLocalization.injective Bp hS).nontrivial
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Bp
  refine ⟨M, hM, fun M' hM' ↦ ?_⟩
  have : M'.IsMaximal := hM'
  have hQ : M'.comap (algebraMap B Bp) = M.comap (algebraMap B Bp) :=
    eq_of_comap_eq_of_pow_mem hn hpow
      ((comap_comap_maximal_localization p M').trans (comap_comap_maximal_localization p M).symm)
  have e1 := IsLocalization.map_under S Bp M'
  have e2 := IsLocalization.map_under S Bp M
  simp only [Ideal.under] at e1 e2
  rw [← e1, hQ, e2]

/-- **Generic regularity descends along finite radicial extensions** (Stacks Lemma
15.48.4 in the finite radicial case).

Divergence from Stacks: Stacks allows any injective finite-type map of domains
(using generic flatness); here `B` is finite over `A` and a fixed power of every
element of `B` lies in `A`. -/
@[stacks 07PA "finite radicial extensions"]
theorem isGenericallyRegular_of_finite_of_pow_mem [IsDomain A] [IsNoetherianRing A]
    [IsDomain B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ b : B, b ^ n ∈ Set.range (algebraMap A B)) (h' : B) (hh' : h' ≠ 0)
    (hreg : ∀ Q : PrimeSpectrum B, h' ∉ Q.asIdeal → Q ∈ primeRegularLocus B) :
    IsGenericallyRegular A := by
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Module.freeLocus A B := by
    have : IsLocalization.AtPrime (FractionRing A) (⊥ : Ideal A) := by
      unfold IsLocalization.AtPrime
      rw [Ideal.primeCompl_bot]
      infer_instance
    rw [Module.mem_freeLocus_iff_tensor _ (FractionRing A)]
    infer_instance
  obtain ⟨_, ⟨r, rfl⟩, hbr, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hbot Module.isOpen_freeLocus
  have hr0 : r ≠ 0 := fun h ↦ hbr (by simp [h])
  obtain ⟨a₀, ha₀⟩ := hpow h'
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha₀
    exact hh' ((pow_eq_zero_iff hn.ne').mp ha₀.symm)
  refine ⟨a₀ * r, mul_ne_zero ha₀0 hr0, fun Q hQ ↦ ?_⟩
  set p := Q.asIdeal
  have ha₀p : a₀ ∉ p := fun h ↦ hQ (p.mul_mem_right _ h)
  have hrp : r ∉ p := fun h ↦ hQ (p.mul_mem_left _ h)
  set S := Algebra.algebraMapSubmonoid B p.primeCompl
  set Bp := Localization S
  set Ap := Localization.AtPrime p
  have : IsLocalRing Bp := isLocalRing_localization_of_pow_mem hinj hn hpow p
  have hfree : Module.Free Ap Bp :=
    (Module.mem_freeLocus_of_isLocalization Q Ap Bp
      (IsScalarTower.toAlgHom A B Bp).toLinearMap).mp (hr hrp)
  -- regularity of `B_p`
  set m := maximalIdeal Bp
  set Q' := m.comap (algebraMap B Bp)
  have hQ'A : Q'.comap (algebraMap A B) = p := comap_comap_maximal_localization p m
  have hh'Q' : h' ∉ Q' := by
    intro hm
    have : algebraMap A B a₀ ∈ Q' := ha₀ ▸ Q'.pow_mem_of_mem hm n hn
    exact ha₀p (hQ'A ▸ (Ideal.mem_comap.mpr this))
  have hQ'reg : IsRegularLocalRing (Localization.AtPrime Q') := hreg ⟨Q', inferInstance⟩ hh'Q'
  have : IsRegularLocalRing (Localization.AtPrime m) :=
    (isRegularLocalRing_localizationAtPrime_iff S Bp m).mpr hQ'reg
  have : IsRegularLocalRing Bp :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.atUnits Bp m.primeCompl
      (S := Localization.AtPrime m)
      (fun x hx ↦ (IsLocalRing.notMem_maximalIdeal.mp hx))).symm.toRingEquiv
  exact isRegularLocalRing_of_free_of_isRegularLocalRing (A := Ap) (B := Bp)

#print axioms eq_of_comap_eq_of_pow_mem
#print axioms comap_comap_maximal_localization
#print axioms isLocalRing_localization_of_pow_mem
#print axioms isGenericallyRegular_of_finite_of_pow_mem

end Pcf
