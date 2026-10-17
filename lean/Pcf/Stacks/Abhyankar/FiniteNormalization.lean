/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.AffineTame
public import Pcf.Stacks.Abhyankar.Scheme.AffineNormalization
public import Pcf.Stacks.Abhyankar.Scheme.TameBridge
public import Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame

/-!
# The normalization is finite (Stacks Tag `0EYH`, first assertion, affine form)

Setting: `R` Noetherian, `a ∈ R` a nonzerodivisor with `R ⧸ (a)` regular, `S` an `R`-algebra
with `S[1/a] = R[1/a] ⊗_R S` finite over `R[1/a]` and étale away from `a` (so
`Y = Spec S[1/a] → X ∖ D` is finite étale, the hypothesis of Tag `0EYG`), and `S` the integral
closure of `R` in `S[1/a]` (the normalization `Y'` of `X = Spec R` in `Y`).  If `S[1/a]` is tamely
ramified in codimension one along `V(a)`, then `S` is finite over `R`
(`Pcf.Stacks.finite_of_isIntegralClosure_away`); the characteristic-zero case is
`Pcf.Stacks.finite_of_isIntegralClosure_away_of_isUnit_natCast`.

With this, the public affine theorems are stated without assuming the normalization finite:
`Pcf.Stacks.abhyankarLemma : ∀ R S a, AbhyankarLemma R S a` and
`Pcf.Stacks.abhyankarLemmaTame : ∀ R S a, AbhyankarLemmaTame R S a`, deduced from the
finite-normalization forms `Pcf.Stacks.abhyankarLemmaOfFinite` and
`Pcf.Stacks.abhyankarLemmaTameOfFinite`.

## Route (Stacks proof of `0EYH` → Lean)

Stacks: "taking the normalization of `X` in `Y` commutes with étale base change … we may prove
the statements … étale locally on `X`; by `0EYG` we may assume `Y` is a finite disjoint union of
`A_f[x]/(x^e - f)`", whose normalization `A[x]/(x^e - f)` is finite.  Here, with `B = S[1/a]`:
* `B` is finite étale over `R_a` (`etale_away`; the étale hypothesis is pointwise formal
  étaleness, the finiteness hypothesis supplies finite presentation);
* the codimension-one tameness of `S` is read on the chart `Spec B → Spec R_a ⊂ Spec R`
  (`isTamelyRamifiedAlongDivisor_of_isTamelyRamifiedInCodimensionOneAlong`): at a height-one prime `𝔭 ∋ a`, the
  integral closure of `R_𝔭` in `K_𝔭 ⊗_R B` is a localization of `S`, and tameness is invariant
  under localization (`isTamelyRamifiedAt_map_of_isLocalization`);
* `0EYG` at every point of `V(a)` (`hasLocalizedStandardCoverAt_of_tame`, which applies the
  finite-normalization theorem at the regular local rings `R_y`, where finiteness is classical,
  Stacks `032L`) and the descent of finiteness along the étale-local structure
  (`integralClosure_finite`) give `integralClosure R B` finite over `R`; and `S ≅ integralClosure
  R B`.

## Why "`S[1/a]` finite over `R[1/a]`" is assumed

The étale hypothesis `∀ w ∌ a, Algebra.IsEtaleAt R w` is formal étaleness of the local rings and
does not give finite type.  For `R = ℚ[t]_{(t)}`, `a = t`, `L = ℚ(ζ_{ℓ^∞})(t)` and `S` the integral
closure of `R` in `L`, every other hypothesis of `AbhyankarLemma` holds (`S[1/t] = L` is an
ind-étale field extension of `ℚ(t)`, and every positive integer is invertible), but `S` is not
finite over `R`, and the conclusion fails (it would make `S` finite by faithfully flat descent along
an étale neighbourhood of the closed point).  So the finiteness of `Y → X ∖ D` from Stacks `0EYG`
is kept as the hypothesis `Module.Finite R[1/a] (R[1/a] ⊗_R S)`.

The two hypotheses together are exactly "`Y = Spec S[1/a] → X ∖ D = Spec R[1/a]` is finite
étale": given them, `S[1/a]` is étale over `R[1/a]` (`etale_away`: finite over the Noetherian
`R[1/a]`, hence of finite presentation, and formally étale at every prime because `R → R[1/a]` is
a localization); conversely, if `S[1/a]` is finite étale over `R[1/a]`, then `R[1/a] ⊗_R S` is
finite and each `S_w`, `a ∉ w`, is a localization of `S[1/a]`, formally étale over `R[1/a]` and
hence over `R`.
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing

set_option linter.style.haveILetI false

namespace Pcf.Stacks.SchemeLevel.AffineTame

open Pcf.Stacks.SchemeLevel

/-! ### Transport along an equality of primes -/

/-- `IsTamelyRamifiedOver (R_P) (K_P ⊗_R B)` depends only on the prime `P`. -/
theorem isTamelyRamifiedOver_congr {R : Type u} [CommRing R] (B : Type u) [CommRing B]
    [Algebra R B] {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (h : P = Q)
    (H : IsTamelyRamifiedOver (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P) ⊗[R] B)) :
    IsTamelyRamifiedOver (Localization.AtPrime Q)
      (FractionRing (Localization.AtPrime Q) ⊗[R] B) := by
  subst h
  exact H

/-- `ringKrullDim R_P` depends only on the prime `P`. -/
theorem ringKrullDim_atPrime_congr {R : Type u} [CommRing R] {P Q : Ideal R} [P.IsPrime]
    [Q.IsPrime] (h : P = Q) :
    ringKrullDim (Localization.AtPrime P) = ringKrullDim (Localization.AtPrime Q) := by
  subst h
  rfl

/-- For an integral extension, a prime lying over a minimal prime of `I` is minimal over `I S`
(incomparability). -/
theorem mem_minimalPrimes_map_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] {I : Ideal R} (q : Ideal S) [q.IsPrime]
    (hq : q.under R ∈ I.minimalPrimes) : q ∈ (I.map (algebraMap R S)).minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr hq.1.2⟩, fun q' ⟨hq', hIq'⟩ hle ↦ ?_⟩
  haveI := hq'
  by_contra hne
  have hlt : q' < q := lt_of_le_of_ne hle fun h ↦ hne (h ▸ le_rfl)
  have hlt' := Ideal.IsIntegral.under_lt_under (R := R) hlt
  exact (hlt'.not_ge) (hq.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hIq'⟩ hlt'.le)

/-! ### The chart is tame: from `S` to `K_𝔭 ⊗_R B` -/

section ChartTame

variable {R : Type u} [CommRing R] (a : R) (Ra : Type u) [CommRing Ra] [Algebra R Ra]
  [IsLocalization.Away a Ra]
  (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]

attribute [local instance] algebraLocalizationAtContraction genericFibreAtContractionAlgebra normalizationAtContractionAlgebra

/-- `B_y = R_y ⊗_R B` as a `B`-algebra (via `toLocalizedCover`). -/
@[instance_reducible]
noncomputable def localizedCoverAlgebra (y : Ideal R) [y.IsPrime] : Algebra B (LocalizedCover B y) :=
  (toLocalizedCover B y).toAlgebra

attribute [local instance] localizedCoverAlgebra

instance isScalarTower_localizedCover (y : Ideal R) [y.IsPrime] : IsScalarTower R B (LocalizedCover B y) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    change (algebraMap R (Localization.AtPrime y) r) ⊗ₜ[R] (1 : B) =
      (1 : Localization.AtPrime y) ⊗ₜ[R] algebraMap R B r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- `B_y` is the localization of `B` at `R ∖ y`. -/
theorem isLocalization_localizedCover (y : Ideal R) [y.IsPrime] :
    IsLocalization (Algebra.algebraMapSubmonoid B y.primeCompl) (LocalizedCover B y) := by
  letI : Algebra B (Localization.AtPrime y ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  exact IsLocalization.tensorRight (Localization.AtPrime y) y.primeCompl

/-- The map `integralClosure R B → N_y` induced by `B → B_y`. -/
noncomputable def integralClosureToLocalizedNormalization (y : Ideal R) [y.IsPrime] :
    integralClosure R B →+* LocalizedNormalization B y where
  toFun x := ⟨algebraMap B (LocalizedCover B y) x.1, by
    have hx : IsIntegral R x.1 := x.2
    exact (hx.map (IsScalarTower.toAlgHom R B (LocalizedCover B y))).tower_top⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x z := Subtype.ext (map_mul (algebraMap B (LocalizedCover B y)) x.1 z.1)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x z := Subtype.ext (map_add (algebraMap B (LocalizedCover B y)) x.1 z.1)

/-- `N_y` as an algebra over `integralClosure R B`. -/
@[instance_reducible]
noncomputable def localizedNormalizationAlgebra (y : Ideal R) [y.IsPrime] : Algebra (integralClosure R B) (LocalizedNormalization B y) :=
  (integralClosureToLocalizedNormalization B y).toAlgebra

attribute [local instance] localizedNormalizationAlgebra

instance isScalarTower_localizedNormalization (y : Ideal R) [y.IsPrime] :
    IsScalarTower (integralClosure R B) (LocalizedNormalization B y) (LocalizedCover B y) := by
  refine ⟨fun x c s ↦ ?_⟩
  change ((integralClosureToLocalizedNormalization B y x * c : LocalizedNormalization B y) : LocalizedCover B y) * s = (x : B) • (c * s)
  rw [Subalgebra.coe_mul, Algebra.smul_def, mul_assoc]
  rfl

instance isScalarTower_integralClosure_localizedNormalization (y : Ideal R) [y.IsPrime] :
    IsScalarTower R (integralClosure R B) (LocalizedNormalization B y) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    apply Subtype.ext
    change algebraMap R (LocalizedCover B y) r = algebraMap B (LocalizedCover B y) (algebraMap R B r)
    rw [← IsScalarTower.algebraMap_apply]

/-- `N_y` is the localization of `integralClosure R B` at `R ∖ y` (integral closure commutes with
localization). -/
theorem isLocalization_localizedNormalization (y : Ideal R) [y.IsPrime] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R B) y.primeCompl) (LocalizedNormalization B y) := by
  haveI := isLocalization_localizedCover B y
  exact IsLocalization.integralClosure (R := R) (S := B) (Rf := Localization.AtPrime y)
    (Sf := LocalizedCover B y) y.primeCompl

variable (S : Type u) [CommRing S] [Algebra R S] [Algebra S B] [IsScalarTower R S B]

include Ra in
/-- At a prime `y ∋ a` with `dim R_y = 1`, tameness of the normalization `S` gives tameness of
`K_y ⊗_R B` over `R_y` (stated with the prime `𝔭 = 𝔪_{R_y} ∩ R` of the chart machinery, which is
`y`). -/
theorem isTamelyRamifiedOver_of_isTamelyRamifiedInCodimensionOneAlong [IsNoetherianRing R]
    (ha : a ∈ nonZeroDivisors R) [IsRegularRing (R ⧸ Ideal.span {a})]
    [IsIntegralClosure S R B] (htame : IsTamelyRamifiedInCodimensionOneAlong R S a)
    (y : Ideal R) [y.IsPrime] (hy : a ∈ y) (hdim : ringKrullDim (Localization.AtPrime y) = 1) :
    IsTamelyRamifiedOver (Localization.AtPrime (contraction y (maximalIdeal (Localization.AtPrime y))))
      (GenericFibreAtContraction B y (maximalIdeal (Localization.AtPrime y))) := by
  intro m hm
  set Ry := Localization.AtPrime y
  set p' : Ideal Ry := maximalIdeal Ry
  have hPy : contraction y p' = y := IsLocalization.AtPrime.under_maximalIdeal Ry y
  have hap' : a ∈ contraction y p' := by rw [hPy]; exact hy
  have hdim' : ringKrullDim (Localization.AtPrime (contraction y p')) = 1 := by
    rw [ringKrullDim_atPrime_congr hPy]; exact hdim
  haveI : IsRegularLocalRing (Localization.AtPrime (contraction y p')) :=
    Pcf.Stacks.isRegularLocalRing_atPrime_of_regular_principal_quotient a ha (contraction y p') hap'
  haveI : IsDomain (Localization.AtPrime (contraction y p')) :=
    Pcf.Stacks.isDomain_of_isRegularLocalRing _
  haveI : IsDiscreteValuationRing (Localization.AtPrime (contraction y p')) :=
    Pcf.Stacks.isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one _ hdim'
  haveI := isLocalization_genericFibreAtContraction a Ra B y ha p' hap'
  haveI := isScalarTower_localizationAtContraction y p'
  haveI := isLocalization_localizationAtContraction y p'
  haveI := isLocalization_normalizationAtContraction B y p'
  set Rp := Localization.AtPrime (contraction y p')
  haveI : m.IsPrime := hm.isPrime
  haveI := hm
  -- the prime `q` of `N_y` below `m`
  let q : Ideal (LocalizedNormalization B y) := m.comap (algebraMap (LocalizedNormalization B y) (NormalizationAtContraction B y p'))
  have hmRp : m.under Rp = maximalIdeal Rp :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rp) (S := NormalizationAtContraction B y p') m)
  have hqy : q.under Ry = p' := by
    have : q.under Ry = (m.under Rp).under Ry := by
      change (m.under (LocalizedNormalization B y)).under Ry = _
      rw [Ideal.under_under (A := Ry) (B := LocalizedNormalization B y) m,
        Ideal.under_under (A := Ry) (B := Rp) m]
    rw [this, hmRp]
    exact IsLocalization.AtPrime.under_maximalIdeal Rp p'
  have hmq : q.map (algebraMap (LocalizedNormalization B y) (NormalizationAtContraction B y p')) = m :=
    IsLocalization.map_under (Algebra.algebraMapSubmonoid (LocalizedNormalization B y) p'.primeCompl) (NormalizationAtContraction B y p') m
  -- the prime `q₀` of `N = integralClosure R B` below `q`
  haveI := isLocalization_localizedNormalization B y
  let q0 : Ideal (integralClosure R B) := q.comap (algebraMap (integralClosure R B) (LocalizedNormalization B y))
  have hq0 : q0.under R = y := by
    have : q0.under R = (q.under Ry).under R := by
      change (q.under (integralClosure R B)).under R = _
      rw [Ideal.under_under (A := R) (B := integralClosure R B) q,
        Ideal.under_under (A := R) (B := Ry) q]
    rw [this, hqy]
    exact hPy
  have hqmap : q0.map (algebraMap (integralClosure R B) (LocalizedNormalization B y)) = q :=
    IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure R B) y.primeCompl)
      (LocalizedNormalization B y) q
  -- the prime `q₁` of `S` corresponding to `q₀`
  let e : S ≃ₐ[R] integralClosure R B := IsIntegralClosure.equiv R S B (integralClosure R B)
  let q1 : Ideal S := q0.comap (e : S →+* integralClosure R B)
  have hq1 : q1.under R = y := by
    rw [← hq0]
    change Ideal.comap _ (Ideal.comap _ q0) = Ideal.comap _ q0
    rw [Ideal.comap_comap]
    congr 1
    ext r
    exact congrArg Subtype.val (e.commutes r)
  have hyh : y.height = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height y Ry
    rw [hdim] at h
    exact_mod_cast h.symm
  have hymin : y ∈ (Ideal.span {a}).minimalPrimes :=
    (Pcf.Stacks.mem_minimalPrimes_span_singleton_iff_height_eq_one ha y).mpr ⟨hyh, hy⟩
  haveI : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R B
  have h1 : q1.under R ∈ (Ideal.span {a}).minimalPrimes := hq1 ▸ hymin
  have hS : IsTamelyRamifiedAt R S ⟨q1, inferInstance⟩ :=
    htame ⟨q1, inferInstance⟩ h1 (mem_minimalPrimes_map_of_isIntegral q1 h1)
  have hN : IsTamelyRamifiedAt R (integralClosure R B) ⟨q0, inferInstance⟩ :=
    Pcf.Stacks.IsTamelyRamifiedAt.of_ringEquiv (RingEquiv.refl R) e.toRingEquiv
      (fun x ↦ e.commutes x) (q := ⟨q1, inferInstance⟩) rfl hS
  have hNy : IsTamelyRamifiedAt Ry (LocalizedNormalization B y) ⟨q, inferInstance⟩ := by
    have := isTamelyRamifiedAt_map_of_isLocalization y Ry (LocalizedNormalization B y) ⟨q0, inferInstance⟩ hq0 hN
    have heq : (⟨q, inferInstance⟩ : PrimeSpectrum (LocalizedNormalization B y)) =
        ⟨q0.map (algebraMap (integralClosure R B) (LocalizedNormalization B y)),
          isPrime_map_localizationAtPrime y (LocalizedNormalization B y) q0 hq0⟩ := PrimeSpectrum.ext hqmap.symm
    rw [heq]
    exact this
  have := isTamelyRamifiedAt_map_of_isLocalization p' Rp (NormalizationAtContraction B y p') ⟨q, inferInstance⟩ hqy hNy
  have heq : (⟨m, hm.isPrime⟩ : PrimeSpectrum (NormalizationAtContraction B y p')) =
      ⟨q.map (algebraMap (LocalizedNormalization B y) (NormalizationAtContraction B y p')), isPrime_map_localizationAtPrime p' (NormalizationAtContraction B y p') q hqy⟩ :=
    PrimeSpectrum.ext hmq.symm
  rw [heq]
  exact this

include Ra in
/-- **The chart `Spec B → Spec R_a ⊂ Spec R` is tame in codimension one** (`IsTamelyRamifiedAlongDivisor`) when the
normalization `S` of `R` in `B` is tamely ramified in codimension one along `V(a)`
(`IsTamelyRamifiedInCodimensionOneAlong`): at a height-one prime `𝔭 ∋ a`, the integral closure of
`R_𝔭` in `K_𝔭 ⊗_R B` is the localization of `S` at `𝔭`. -/
theorem isTamelyRamifiedAlongDivisor_of_isTamelyRamifiedInCodimensionOneAlong [IsNoetherianRing R]
    (ha : a ∈ nonZeroDivisors R) [IsRegularRing (R ⧸ Ideal.span {a})]
    [IsIntegralClosure S R B] (htame : IsTamelyRamifiedInCodimensionOneAlong R S a) :
    IsTamelyRamifiedAlongDivisor a B := by
  intro p hp hap hdim
  have hP : contraction p (maximalIdeal (Localization.AtPrime p)) = p :=
    IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p
  exact isTamelyRamifiedOver_congr B hP
    (isTamelyRamifiedOver_of_isTamelyRamifiedInCodimensionOneAlong a Ra B S ha htame p hap hdim)

end ChartTame

/-! ### The chart is tame in characteristic zero -/

section ChartTameCharZero

variable {R : Type u} [CommRing R] (a : R) (Ra : Type u) [CommRing Ra] [Algebra R Ra]
  [IsLocalization.Away a Ra]
  (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]

include Ra in
/-- **The chart is tame when every positive integer is invertible.**  At a height-one prime
`𝔭 ∋ a`, `R_𝔭` is a discrete valuation ring and `K_𝔭 ⊗_R B` is finite étale over `K_𝔭`, so the
integral closure of `R_𝔭` in it is finite (`finite_integralClosure_of_etale_fractionRing`), and
every prime of a finite algebra is tame in characteristic zero
(`isTamelyRamifiedAt_of_isUnit_natCast`). -/
theorem isTamelyRamifiedAlongDivisor_of_isUnit_natCast [IsNoetherianRing R] (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span {a})] [Module.Finite Ra B] [Algebra.Etale Ra B]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) : IsTamelyRamifiedAlongDivisor a B := by
  intro p hp hap _
  set Rp := Localization.AtPrime p
  haveI : IsRegularLocalRing Rp :=
    Pcf.Stacks.isRegularLocalRing_atPrime_of_regular_principal_quotient a ha p hap
  haveI : IsDomain Rp := Pcf.Stacks.isDomain_of_isRegularLocalRing _
  haveI : IsIntegrallyClosed Rp := Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing _
  set K := FractionRing Rp
  set L := K ⊗[R] B
  haveI : Algebra.Etale R Ra := Algebra.Etale.of_isLocalizationAway a
  haveI : Algebra.Etale R B := Algebra.Etale.comp R Ra B
  have haK : IsUnit (algebraMap R K a) := by
    rw [IsScalarTower.algebraMap_apply R Rp K]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (IsLocalization.map_nonZeroDivisors_le p.primeCompl Rp ⟨a, ha, rfl⟩)).isUnit
  let φ : Ra →+* K := IsLocalization.Away.lift a haK
  let ψ : B →+* L := (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom
  have hcomp : (algebraMap K L).comp φ = ψ.comp (algebraMap Ra B) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift, IsLocalization.lift_eq, ψ]
    rw [← IsScalarTower.algebraMap_apply R Ra B]
    change algebraMap K L (algebraMap R K r) =
      (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)) (algebraMap R B r)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsIntegral Ra B := Algebra.IsIntegral.of_finite Ra B
  have hint : Algebra.IsIntegral K L := by
    constructor
    intro x
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => exact hx.add hz
    | tmul k b =>
      have h2 : IsIntegral K (ψ b) :=
        IsIntegral.map_of_comp_eq φ ψ hcomp (Algebra.IsIntegral.isIntegral b)
      have e : k ⊗ₜ[R] b = k • ((1 : K) ⊗ₜ[R] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact h2.smul k
  haveI : Module.Finite K L := Algebra.IsIntegral.finite
  haveI : Module.Finite Rp (integralClosure Rp L) :=
    finite_integralClosure_of_etale_fractionRing Rp L
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Rp) := fun n hn ↦ by
    simpa only [map_natCast] using (hnat n hn).map (algebraMap R Rp)
  intro m hm
  exact Pcf.Stacks.isTamelyRamifiedAt_of_isUnit_natCast Rp (integralClosure Rp L) hunit _

end ChartTameCharZero

end Pcf.Stacks.SchemeLevel.AffineTame

/-! ### Finiteness of the normalization and the public theorems -/

namespace Pcf.Stacks

open SchemeLevel SchemeLevel.AffineTame

section Finite

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- `S[1/a]` as an `R[1/a]`-algebra. -/
@[instance_reducible]
noncomputable def awayAlgebra (a : R) :
    Algebra (Localization.Away a) (Localization.Away (algebraMap R S a)) :=
  (Localization.awayMap (algebraMap R S) a).toAlgebra

attribute [local instance] awayAlgebra

instance awayAlgebra_isScalarTower (a : R) :
    IsScalarTower R (Localization.Away a) (Localization.Away (algebraMap R S a)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply]

/-- `S[1/a]` is finite over `R[1/a]` when `R[1/a] ⊗_R S` is (they are isomorphic). -/
theorem finite_away_of_finite_tensor {a : R}
    (hfin : Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] S)) :
    Module.Finite (Localization.Away a) (Localization.Away (algebraMap R S a)) := by
  have hlm : IsLocalizedModule (Submonoid.powers a)
      (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S a))).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid_powers]
    infer_instance
  exact Module.Finite.equiv
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (Localization.Away a) _).mp
      hlm).equiv

/-- If `S` is étale over `R` at every prime not containing `a` (formally étale local rings), then
`S[1/a]` is formally étale over `R`. -/
theorem formallyEtale_away {a : R}
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) :
    Algebra.FormallyEtale R (Localization.Away (algebraMap R S a)) := by
  rw [← Algebra.etaleLocus_eq_univ_iff]
  ext P
  simp only [Set.mem_univ, iff_true, Algebra.mem_etaleLocus_iff]
  set w : Ideal S := P.asIdeal.comap (algebraMap S (Localization.Away (algebraMap R S a)))
  have hw : algebraMap R S a ∉ w := fun h ↦ P.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit _))
  haveI := hetale ⟨w, inferInstance⟩ hw
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (algebraMap R S a)) P.asIdeal
  exact Algebra.FormallyEtale.of_equiv (e.restrictScalars R)

/-- `S[1/a]` is étale over `R[1/a]` under the hypotheses of `0EYG` on `Y = Spec S[1/a]`. -/
theorem etale_away [IsNoetherianRing R] {a : R}
    (hfin : Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] S))
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) :
    Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R S a)) := by
  haveI := formallyEtale_away hetale
  haveI : IsLocalization ((Submonoid.powers a).map (algebraMap R S))
      (Localization.Away (algebraMap R S a)) := by
    rw [Submonoid.map_powers]
    infer_instance
  haveI : Algebra.FormallyEtale (Localization.Away a) (Localization.Away (algebraMap R S a)) :=
    Algebra.FormallyEtale.localization_base (Rₘ := Localization.Away a)
      (Sₘ := Localization.Away (algebraMap R S a)) (Submonoid.powers a)
  haveI : IsNoetherianRing (Localization.Away a) :=
    IsLocalization.isNoetherianRing (Submonoid.powers a) _ inferInstance
  haveI := finite_away_of_finite_tensor hfin
  haveI : Algebra.FinitePresentation (Localization.Away a)
      (Localization.Away (algebraMap R S a)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- **The normalization is finite, given a tame chart** (Stacks Tag `0EYH`, first assertion, affine
form): `0EYG` at every point of `V(a)` (`hasLocalizedStandardCoverAt_of_tame`, with a
finite-normalization theorem `hA` at the local rings `R_y`) and faithfully flat descent of
finiteness (`integralClosure_finite`). -/
theorem finite_of_isIntegralClosure_away_of_isTamelyRamifiedAlongDivisor [IsNoetherianRing R] {a : R}
    (ha : a ∈ nonZeroDivisors R) [IsRegularRing (R ⧸ Ideal.span {a})]
    (hfin : Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] S))
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))]
    (hchart : IsTamelyRamifiedAlongDivisor a (Localization.Away (algebraMap R S a)))
    (hA : ∀ y : PrimeSpectrum R, ∀ (S' : Type u) [CommRing S']
      [Algebra (Localization.AtPrime y.asIdeal) S'] (b : Localization.AtPrime y.asIdeal),
        AbhyankarLemmaTameOfFinite (Localization.AtPrime y.asIdeal) S' b) :
    Module.Finite R S := by
  haveI := finite_away_of_finite_tensor hfin
  haveI := etale_away hfin hetale
  have hloc : ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
      HasLocalizedStandardCoverAt a (Localization.Away (algebraMap R S a)) y := fun y hy ↦
    hasLocalizedStandardCoverAt_of_tame a ha (Localization.Away a) _ hchart y hy (hA y)
  haveI := integralClosure_finite a (Localization.Away a) _ ha hloc
  exact Module.Finite.equiv
    (IsIntegralClosure.equiv R S (Localization.Away (algebraMap R S a))
      (integralClosure R (Localization.Away (algebraMap R S a)))).symm.toLinearEquiv

/-- **The normalization is finite** (Stacks Tag `0EYH`, first assertion, affine form).  Let `R` be
Noetherian, `a` a nonzerodivisor with `R ⧸ (a)` regular, `S[1/a] = R[1/a] ⊗_R S` finite over
`R[1/a]` and étale away from `a`, `S` the integral closure of `R` in `S[1/a]`, tamely ramified in
codimension one along `V(a)`.  Then `S` is finite over `R`.  Stacks deduces this from `0EYG`
étale locally; so does the proof (see the module docstring). -/
@[stacks 0EYH "first assertion (the normalization is finite), affine form"]
theorem finite_of_isIntegralClosure_away [IsNoetherianRing R] {a : R}
    (ha : a ∈ nonZeroDivisors R) [IsRegularRing (R ⧸ Ideal.span {a})]
    (hfin : Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] S))
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))]
    (htame : IsTamelyRamifiedInCodimensionOneAlong R S a) :
    Module.Finite R S :=
  finite_of_isIntegralClosure_away_of_isTamelyRamifiedAlongDivisor ha hfin hetale
    (isTamelyRamifiedAlongDivisor_of_isTamelyRamifiedInCodimensionOneAlong a (Localization.Away a) _ S ha htame)
    fun _ S' _ _ b ↦ abhyankarLemmaTameOfFinite _ S' b

/-- **The normalization is finite, characteristic zero** (Stacks Tag `0EYH`, first assertion,
affine form, every positive integer invertible in `R`; no tameness hypothesis is needed).  The
local input is the characteristic-zero theorem `abhyankarLemmaOfFinite` (through
`SchemeLevel.abhyankarLemmaTame_of_isUnit_natCast`), whose proof is the shared tame proof with
tameness supplied by `isTamelyRamifiedInCodimensionOneAlong_of_isUnit_natCast`. -/
@[stacks 0EYH "first assertion (the normalization is finite), affine form; every positive integer \
  invertible"]
theorem finite_of_isIntegralClosure_away_of_isUnit_natCast [IsNoetherianRing R] {a : R}
    (ha : a ∈ nonZeroDivisors R) [IsRegularRing (R ⧸ Ideal.span {a})]
    (hfin : Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] S))
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) :
    Module.Finite R S := by
  haveI := finite_away_of_finite_tensor hfin
  haveI := etale_away hfin hetale
  exact finite_of_isIntegralClosure_away_of_isTamelyRamifiedAlongDivisor ha hfin hetale
    (isTamelyRamifiedAlongDivisor_of_isUnit_natCast a (Localization.Away a) _ ha hnat)
    fun y S' _ _ b ↦ abhyankarLemmaTame_of_isUnit_natCast _ S' b fun n hn ↦ by
      simpa only [map_natCast] using (hnat n hn).map (algebraMap R (Localization.AtPrime y.asIdeal))

end Finite

/-- **Abhyankar's lemma for a regular divisor, tame case (Stacks Tags `0EYG` and `0EYH`)**, in
pcf's affine form `Pcf.Stacks.AbhyankarLemmaTame`: `Y = Spec S[1/a] → X ∖ D` finite étale and
tamely ramified in codimension `1` (`IsTamelyRamifiedInCodimensionOneAlong`, Stacks `0BSE` with
`09E9`), in any characteristic, with `S` the normalization of `R` in `S[1/a]`.

Comparison with the tags (restrictions, all part of the statement `AbhyankarLemmaTame`):
* *Affine form*: `X = Spec R` with `R` Noetherian and `D = V(a)`, `a` a nonzerodivisor with
  `R ⧸ (a)` regular (`D` an effective Cartier divisor which is a regular scheme).
* *Conclusion shape*: the `0EYH` local-structure form at every point `y ∈ V(a)`: an étale
  neighbourhood `R → R'` over `y` with `R'` Noetherian, `a` a nonzerodivisor with `R' ⧸ (a)`
  regular, and `R' ⊗_R S` a finite product of `R'[x]/(x^e - u a)` with `e` invertible in `R'` and
  `u` a unit of `R'`.  Points outside `D` (the tag's trivial case) are not treated.

The normalization `S` is not assumed finite over `R`: its finiteness (first assertion of `0EYH`) is
`finite_of_isIntegralClosure_away`, and the theorem is then `abhyankarLemmaTameOfFinite`. -/
@[stacks 0EYG "affine form; Y -> X \\ D finite etale as: R[1/a] ⊗ S finite over R[1/a] and \
    S etale at primes not containing a; tamely ramified in codimension 1, any characteristic; \
    normalization (0EYH) form at points of D; pieces R'[x]/(x^e - f), f = u_i a",
  stacks 0EYH "affine local-structure clause at points of D, normalization proved finite; \
    Y -> X \\ D finite etale as: R[1/a] ⊗ S finite over R[1/a] and S etale at primes not \
    containing a; tamely ramified in codimension 1, any characteristic; pieces R'[x]/(x^e - f), \
    f = u_i a"]
theorem abhyankarLemmaTame (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    AbhyankarLemmaTame R S a := by
  intro hR ha hreg hfin hetale hint htame y hy
  haveI := hreg
  haveI := hint
  exact abhyankarLemmaTameOfFinite R S a hR ha hreg
    (finite_of_isIntegralClosure_away ha hfin hetale htame) hetale hint htame y hy

/-- **Abhyankar's lemma for a regular divisor (Stacks Tags `0EYG` and `0EYH`)**, in pcf's affine
characteristic-zero form `Pcf.Stacks.AbhyankarLemma`: every positive integer invertible in `R`
(stronger than the tags' "tamely ramified in codimension one"), `Y = Spec S[1/a] → X ∖ D` finite
étale, `S` the normalization of `R` in `S[1/a]`; the conclusion is the `0EYH` local-structure form
at the points of `D`, as for `abhyankarLemmaTame`.

The normalization `S` is not assumed finite over `R`: its finiteness is
`finite_of_isIntegralClosure_away_of_isUnit_natCast`, and the theorem is then the
characteristic-zero proof `abhyankarLemmaOfFinite`. -/
@[stacks 0EYG "affine; all positive integers invertible; Y -> X \\ D finite etale as: \
    R[1/a] ⊗ S finite over R[1/a] and S etale at primes not containing a; normalization (0EYH) \
    form at points of D; pieces R'[x]/(x^e - f), f = u_i a",
  stacks 0EYH "affine; all positive integers invertible; local structure clause at points of D, \
    normalization proved finite; Y -> X \\ D finite etale as: R[1/a] ⊗ S finite over R[1/a] and \
    S etale at primes not containing a; pieces R'[x]/(x^e - f), f = u_i a"]
theorem abhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    AbhyankarLemma R S a := by
  intro hR ha hreg hfin hetale hint hnat y hy
  haveI := hreg
  haveI := hint
  exact abhyankarLemmaOfFinite R S a hR ha hreg
    (finite_of_isIntegralClosure_away_of_isUnit_natCast ha hfin hetale hnat) hetale hint hnat y hy

end Pcf.Stacks
