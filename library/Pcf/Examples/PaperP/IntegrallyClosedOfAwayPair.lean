/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Integral closedness from two localizations

If `R` is a domain, `s, t ≠ 0`, the localizations `R_s` and `R_t` are integrally closed, and
`t` is a non-zero-divisor modulo every power of `s` (`s^m ∣ a t^n ⇒ s^m ∣ a`), then `R` is
integrally closed, because `R = R_s ∩ R_t` inside `Frac R`. This is the elementary
normality argument used for the hypersurface of `paper-p.tex`,
Example `ex:charp-exceptional-fibre-paper`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.IntegrallyClosedOfAwayPair

set_option linter.style.haveILetI false

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- An element of `Frac R` integral over `R` is `a / s^m` when `R_s` is integrally closed. -/
theorem exists_eq_div_pow (s : R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away s S] [Algebra S K] [IsScalarTower R S K] [IsIntegrallyClosed S]
    (w : K) (hw : IsIntegral R w) :
    ∃ (a : R) (m : ℕ), w * algebraMap R K (s ^ m) = algebraMap R K a := by
  haveI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers s) S K
  have hw' : IsIntegral S w := hw.tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff K).mp inferInstance hw'
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hzm⟩ := IsLocalization.surj (Submonoid.powers s) z
  refine ⟨a, m, ?_⟩
  rw [← hz]
  have := congrArg (algebraMap S K) hzm
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at this
  exact this

/-- **`R = R_s ∩ R_t`.** -/
theorem isIntegrallyClosed_of_away_pair (s t : R) (S T : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away s S] [Algebra S K] [IsScalarTower R S K] [IsIntegrallyClosed S]
    [CommRing T] [Algebra R T]
    [IsLocalization.Away t T] [Algebra T K] [IsScalarTower R T K] [IsIntegrallyClosed T]
    (hs : s ≠ 0)
    (hreg : ∀ (a b : R) (m n : ℕ), a * t ^ n = b * s ^ m → s ^ m ∣ a) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff K]
  intro w hw
  obtain ⟨a, m, ha⟩ := exists_eq_div_pow s S w hw
  obtain ⟨b, n, hb⟩ := exists_eq_div_pow t T w hw
  have hinj := IsFractionRing.injective R K
  have hab : a * t ^ n = b * s ^ m := by
    apply hinj
    rw [map_mul, map_mul, ← ha, ← hb]
    ring
  obtain ⟨c, rfl⟩ := hreg a b m n hab
  refine ⟨c, ?_⟩
  have hs0 : algebraMap R K (s ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ hs)
  apply mul_right_cancel₀ hs0
  rw [ha, map_mul, mul_comm]

end Pcf.Examples.PaperP.IntegrallyClosedOfAwayPair
