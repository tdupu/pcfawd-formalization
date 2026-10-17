/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.DVRKummerBaseChange
public import Pcf.Stacks.Abhyankar.HeightOneKummerTransport
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Abhyankar's lemma for discrete valuation rings, divisibility form (Stacks Tag `0BRM`)

Stacks Lemma 15.116.4 (Tag `0BRM`).  Let `A ⊂ B` be an extension of discrete valuation rings
with ramification index `e`, tame with separable residue extension.  Let `K₁/K` be a finite
extension of the fraction field of `A`, `A₁` the integral closure of `A` in `K₁`, `B₁` the integral
closure of `B` in `L ⊗_K K₁`.  If `e` **divides** the ramification index of `A ⊂ (A₁)_{𝔪ᵢ}`, then
`(A₁)_{𝔪ᵢ} → (B₁)_{𝔪ᵢⱼ}` is formally smooth in the adic topology, i.e. (in this finite
situation) unramified.

The case needed in the proof of Tag `0EYG` is `K₁ = K(π^{1/E})` with `e ∣ E`, so that `A₁` is the
DVR `A[π^{1/E}]` (Tag `09EV`).  pcf's earlier endpoint
(`isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_of_root_mem`) treats the exact case
`E = e` with `B` finite over `A`; this file proves the divisibility case `E = d·e` with no
finiteness of `B` over `A`.

## Mathematical route (verified; this is the route sketched in `StrictHeightOneTransport.lean`,
reorganized around uniformizers)

Let `S = B` be a DVR with uniformizer `π`, let `a = u·πᵉ` with `u ∈ Sˣ`, let `E = d·e` with `e`
invertible in `S`, and let `T` be a DVR with a local `S`-algebra structure containing an element
`x` with `xᴱ = a` and whose fraction field is generated over `Frac S` by `x` (every element of `T`
is a quotient `p(x)/q(x)` of polynomials over `S`).  Then **`x` is a uniformizer of `T`**:

1. In the valuation ring `T` the equation `(xᵈ)ᵉ = πᵉ·u` forces `xᵈ = π·y` with `y` a unit of
   `T` and `yᵉ = u` (`exists_unit_pow_eq_of_pow_mul_eq`; no valuation arithmetic, only
   `ValuationRing.dvd_total`).
2. `U = S[y]/(yᵉ − u)` is the étale Kummer algebra of pcf's exact case; `y ↦ y` gives
   `ψ : U → T`.  Let `𝔪 = ψ⁻¹(𝔪_T)`.  Then `U_𝔪` is a DVR
   (`kummerUnit_localizationAtPrime_isDiscreteValuationRing`) which is formally unramified over
   `S`, so `π` is still a uniformizer of `U_𝔪` (`Algebra.FormallyUnramified.map_maximalIdeal`,
   Stacks `00UW`), and so is `π·y`.
3. `V = U_𝔪[z]/(zᵈ − π·y)` is a DVR with uniformizer `z` (Tag `09EV`,
   `dvrRootAlgebra_isDiscreteValuationRing`), and `z ↦ x` gives a local map `φ : V → T` with
   `Frac V = Frac S(x) = Frac T`.
4. A local map of DVRs that is surjective on fraction fields is surjective
   (`surjective_of_isLocalHom_of_dvr`): write `t = f v / f w`, factor `v = v'ϖⁱ`, `w = w'ϖʲ`; if
   `j ≤ i` then `t ∈ f(V)`, otherwise `f ϖ` divides the unit `f v'`, contradicting locality.
   Hence `φ` is an isomorphism and `𝔪_T = φ(𝔪_V) = (x)`.

This differs from the Stacks proof only in bookkeeping: Stacks adjoins `u^{1/e}` to reduce to
`K₁ = K(π^{1/e})` and then compares ramification indices in a square (Lemma 15.116.3); here the
same étale Kummer algebra `U` and the same root `θ/π_B` appear, and the final comparison is
made by the dominance argument of step 4 instead of multiplicativity of ramification indices.

## Statements

* `surjective_of_isLocalHom_of_dvr` — the dominance lemma (step 4).
* `exists_unit_pow_eq_of_pow_mul_eq` — step 1.
* `maximalIdeal_eq_span_root_of_dvd_and_isSeparable` — **Tag `0BRM`, divisibility form**, the
  two facts of the last paragraph of Stacks' proof: under the hypotheses above, `𝔪_T = (x)`,
  i.e. the ramification index of `T` over the `09EV` DVR `A₁ = A[π^{1/E}]` is one, and the
  residue extension `κ(T)/κ(S)` is separable.  For the second fact, `κ(T)` is the image of the
  residue field of `U_𝔪` (every element of `T` is congruent mod `(x)` to one of `U_𝔪`), which is
  separable over `κ(S)` because `S → U_𝔪` is formally unramified (Stacks `00UW`).  In
  characteristic zero the second fact is automatic; the tame proof of `0EYG` needs it.
* `maximalIdeal_eq_span_root_of_dvd` — the uniformizer clause alone.
* `formallyUnramified_dvrRoot_of_dvd` — **Tag `0BRM`, divisibility form**: with `A ⊂ S` the
  original DVR extension, `a` a uniformizer of `A`, `A₁ = A[x]/(xᴱ − a)`, and `T` as above
  essentially of finite type over `A₁` with separable residue extension, `A₁ → T` is formally
  unramified.

## Divergence from Stacks

* Stacks concludes formal smoothness in the `𝔪ᵢⱼ`-adic topology; for the essentially finite
  type extensions at hand this is equivalent to formal unramifiedness (Stacks `0BRJ`), which is
  what is stated.
* The ring `(B₁)_{𝔪ᵢⱼ}` is replaced by an arbitrary DVR `T` dominating `B` whose fraction field
  is `L(π^{1/E})`; these are exactly the localizations of `B₁` at its maximal ideals.
* The tameness hypothesis is `e` invertible in `S` (as in the rest of pcf's proof of Abhyankar's
  lemma).
* Only the case `K₁ = K(π^{1/E})` is treated.
-/

@[expose] public section

universe u v w

open IsLocalRing Polynomial

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section Dominance

variable {V T : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [CommRing T] [IsDomain T]

/-- **Dominance.**  A local ring map from a DVR to a domain which is surjective "on fraction
fields" (every target element is a quotient `f v / f w`) and does not kill the uniformizer is
surjective. -/
theorem surjective_of_isLocalHom_of_dvr (f : V →+* T) [IsLocalHom f] {ϖ : V}
    (hϖ : Irreducible ϖ) (hϖ0 : f ϖ ≠ 0)
    (hgen : ∀ t : T, ∃ v w : V, f w ≠ 0 ∧ f w * t = f v) :
    Function.Surjective f := by
  intro t
  obtain ⟨v, w, hw, hwt⟩ := hgen t
  have hw0 : w ≠ 0 := fun h ↦ hw (by rw [h, map_zero])
  obtain ⟨j, w', hw'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hϖ
  by_cases hv0 : v = 0
  · refine ⟨0, ?_⟩
    subst hv0
    rw [map_zero] at hwt ⊢
    exact ((mul_eq_zero.mp hwt).resolve_left hw).symm
  obtain ⟨i, v', hv'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hϖ
  rw [hv', hw', map_mul, map_mul, map_pow, map_pow] at hwt
  have hw'unit : f (w'⁻¹ : Vˣ) * f (w' : V) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rcases le_or_gt j i with hji | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
    refine ⟨(w'⁻¹ : Vˣ) * v' * ϖ ^ k, ?_⟩
    have hpow : f ϖ ^ j ≠ 0 := pow_ne_zero _ hϖ0
    have hmid : f w' * t = f v' * f ϖ ^ k := by
      apply mul_left_cancel₀ hpow
      calc f ϖ ^ j * (f w' * t) = f w' * f ϖ ^ j * t := by ring
        _ = f v' * f ϖ ^ (j + k) := hwt
        _ = f ϖ ^ j * (f v' * f ϖ ^ k) := by rw [pow_add]; ring
    calc f ((w'⁻¹ : Vˣ) * v' * ϖ ^ k)
        = f (w'⁻¹ : Vˣ) * (f v' * f ϖ ^ k) := by rw [map_mul, map_mul, map_pow, mul_assoc]
      _ = f (w'⁻¹ : Vˣ) * (f w' * t) := by rw [hmid]
      _ = t := by rw [← mul_assoc, hw'unit, one_mul]
  · exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have hpow : f ϖ ^ i ≠ 0 := pow_ne_zero _ hϖ0
    have hdvd : f ϖ ∣ f (v' : V) := by
      refine ⟨f w' * f ϖ ^ k * t, ?_⟩
      apply mul_left_cancel₀ hpow
      calc f ϖ ^ i * f v' = f v' * f ϖ ^ i := by ring
        _ = f w' * f ϖ ^ (i + k + 1) * t := hwt.symm
        _ = f ϖ ^ i * (f ϖ * (f w' * f ϖ ^ k * t)) := by rw [pow_succ, pow_add]; ring
    have hunit : IsUnit (f ϖ) := isUnit_of_dvd_unit hdvd ((Units.isUnit v').map f)
    exact hϖ.not_isUnit (IsLocalHom.map_nonunit ϖ hunit)

end Dominance

section UnitRoot

variable {T : Type*} [CommRing T] [IsDomain T] [ValuationRing T]

/-- In a valuation domain, `(xᵈ)ᵉ = πᵉ·u` with `u` a unit and `e ≥ 1` forces `xᵈ = π·y` with `y` a
unit satisfying `yᵉ = u`. -/
theorem exists_unit_pow_eq_of_pow_mul_eq {x π u : T} (hu : IsUnit u) {d e : ℕ} (he : 1 ≤ e)
    (h : (x ^ d) ^ e = π ^ e * u) (hπ : π ≠ 0) (hx : x ≠ 0) :
    ∃ y : T, IsUnit y ∧ x ^ d = π * y ∧ y ^ e = u := by
  have he0 : e ≠ 0 := by omega
  rcases ValuationRing.dvd_total π (x ^ d) with ⟨y, hy⟩ | ⟨z, hz⟩
  · have hye : y ^ e = u := by
      apply mul_left_cancel₀ (pow_ne_zero e hπ)
      rw [← mul_pow, ← hy, h]
    exact ⟨y, (isUnit_pow_iff he0).mp (hye ▸ hu), hy, hye⟩
  · have hzu : z ^ e * u = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero e (pow_ne_zero d hx))
      calc (x ^ d) ^ e * (z ^ e * u) = (x ^ d * z) ^ e * u := by rw [mul_pow, mul_assoc]
        _ = π ^ e * u := by rw [hz]
        _ = (x ^ d) ^ e * 1 := by rw [mul_one, h]
    have hz_unit : IsUnit z := (isUnit_pow_iff he0).mp ⟨Units.mkOfMulEqOne _ _ hzu, rfl⟩
    obtain ⟨zu, rfl⟩ := hz_unit
    refine ⟨((zu⁻¹ : Tˣ) : T), Units.isUnit _, ?_, ?_⟩
    · rw [hz, mul_assoc, Units.mul_inv, mul_one]
    · calc ((zu⁻¹ : Tˣ) : T) ^ e = ((zu⁻¹ : Tˣ) : T) ^ e * ((zu : T) ^ e * u) := by
            rw [hzu, mul_one]
        _ = u := by rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]

end UnitRoot

section Divisible

variable (S : Type u) (T : Type v) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra S T]
  [IsLocalHom (algebraMap S T)]

/-- **Abhyankar's lemma for DVRs, divisibility form, with the residue-field clause (Stacks Tag
`0BRM`).**

Let `S` be a DVR with uniformizer `π`, `u ∈ Sˣ`, `e ≥ 1` invertible in `S`, `d ≥ 1`, `T` a DVR
with a local `S`-algebra structure not killing `π`, and `x ∈ T` with `x ^ (d·e) = u·πᵉ` generating
the fraction field of `T` over `Frac(S)`.  Conclusion: `x` is a uniformizer of `T` **and** the
residue field extension `κ(T)/κ(S)` is separable.

This is the content of the last paragraph of Stacks' proof of `0BRM` (`B ⊂ (B₁)_𝔪` has
ramification index one and `κ(𝔪)/κ_B` is separable).  Route: steps 1–4 of the module docstring
exhibit `T` as the image of `V = U_𝔪[z]/(z^d − π y)`, which gives `𝔪_T = (x)`.  For the second
clause, `U = S[y]/(yᵉ − u)` is the étale Kummer algebra; modulo `𝔪_T = (x)` every element of `T` is
congruent to an element of `U_𝔪`, so `κ(U_𝔪) → κ(T)` is surjective, and `κ(U_𝔪)/κ(S)` is separable
because `S → U_𝔪` is formally unramified and essentially of finite type (Stacks `00UW`). -/
@[stacks 0BRM "divisibility form e ∣ E with K₁ = K(π^{1/E}), tame case e ∈ Sˣ; (B₁)_𝔪 \
  replaced by any DVR dominating B with fraction field L(π^{1/E}); conclusions: the root is a \
  uniformizer and the residue extension is separable"]
theorem maximalIdeal_eq_span_root_of_dvd_and_isSeparable
    (π : S) (hπ : Irreducible π) (u : Sˣ) (e : ℕ) (he : 1 ≤ e) (heUnit : IsUnit (e : S))
    (d : ℕ) (hd : 1 ≤ d) (x : T)
    (hx : x ^ (d * e) = algebraMap S T ((u : S) * π ^ e))
    (hπ0 : algebraMap S T π ≠ 0)
    (hgen : ∀ t : T, ∃ p q : S[X], aeval x q ≠ 0 ∧ aeval x q * t = aeval x p) :
    maximalIdeal T = Ideal.span {x} ∧
      Algebra.IsSeparable (ResidueField S) (ResidueField T) := by
  have he0 : e ≠ 0 := by omega
  -- `x ≠ 0` and `x ∈ 𝔪_T`.
  have hx0 : x ≠ 0 := by
    intro h0
    have h : algebraMap S T (u : S) * algebraMap S T π ^ e = 0 := by
      rw [← map_pow, ← map_mul, ← hx, h0, zero_pow (Nat.mul_ne_zero (by omega) he0)]
    rcases mul_eq_zero.mp h with h | h
    · exact (u.map (algebraMap S T : S →* T)).isUnit.ne_zero h
    · exact hπ0 ((pow_eq_zero_iff he0).mp h)
  have hπ_mem : algebraMap S T π ∈ maximalIdeal T := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    exact hπ.not_isUnit (IsLocalHom.map_nonunit π hunit)
  have hx_mem : x ∈ maximalIdeal T := by
    apply (maximalIdeal.isMaximal T).isPrime.mem_of_pow_mem (d * e)
    rw [hx, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπ_mem e (by omega))
  -- Step 1: `x ^ d = π * y`, `y` a unit with `y ^ e = u`.
  obtain ⟨y, hy_unit, hxy, hye⟩ := exists_unit_pow_eq_of_pow_mul_eq (T := T)
    (x := x) (π := algebraMap S T π) (u := algebraMap S T (u : S))
    ((u.map (algebraMap S T : S →* T)).isUnit) he
    (by rw [← pow_mul, hx, map_mul, map_pow, mul_comm]) hπ0 hx0
  -- Step 2: the étale Kummer algebra `U = S[y]/(yᵉ − u)` and its localization `U_𝔪`.
  let U := AdjoinRoot (Pcf.Kummer.kummerPoly u e)
  letI : Module.Free S U := (Pcf.Kummer.kummerPoly_monic u he0).free_adjoinRoot
  letI : Module.Finite S U := (Pcf.Kummer.kummerPoly_monic u he0).finite_adjoinRoot
  letI : Algebra.Etale S U := Pcf.Kummer.etale_adjoinRoot_kummerPoly u he0 heUnit
  have hyU : (Pcf.Kummer.kummerPoly u e).eval₂ (algebraMap S T) y = 0 := by
    simp [Pcf.Kummer.kummerPoly, hye]
  let ψ : U →ₐ[S] T := AdjoinRoot.liftAlgHom _ (Algebra.ofId S T) y hyU
  have hψroot : ψ (AdjoinRoot.root _) = y := AdjoinRoot.liftAlgHom_root _ _ _ _
  let m : Ideal U := (maximalIdeal T).comap ψ.toRingHom
  haveI : m.IsPrime := Ideal.IsPrime.comap _
  have hm : m.under S = maximalIdeal S := by
    have h1 : m.under S = (maximalIdeal T).under S := by
      change Ideal.comap (algebraMap S U) (Ideal.comap ψ.toRingHom (maximalIdeal T)) = _
      rw [Ideal.comap_comap]
      congr 1
      ext s
      simp [ψ]
    rw [h1]
    exact ((IsLocalRing.local_hom_TFAE (algebraMap S T)).out 1 5).mp
      (inferInstance : IsLocalHom (algebraMap S T))
  let Um := Localization.AtPrime m
  letI : IsDomain Um := kummerUnit_localizationAtPrime_isDomain S u e he heUnit m hm
  letI : IsDiscreteValuationRing Um :=
    kummerUnit_localizationAtPrime_isDiscreteValuationRing S π hπ u e he heUnit m hm
  letI : IsLocalHom (algebraMap S Um) :=
    isLocalHom_localizationAtPrime_of_under_eq_maximalIdeal S U m hm
  -- `S → U_𝔪` is formally unramified and essentially of finite type, so `κ(U_𝔪)/κ(S)` is
  -- separable (Stacks `00UW`).
  letI : Algebra.FormallyUnramified S U := inferInstance
  letI : Algebra.FormallyUnramified U Um :=
    Algebra.FormallyUnramified.of_isLocalization m.primeCompl
  letI : Algebra.FormallyUnramified S Um := Algebra.FormallyUnramified.comp S U Um
  letI : Algebra.EssFiniteType S Um := inferInstance
  haveI hsepUm : Algebra.IsSeparable (ResidueField S) (ResidueField Um) := inferInstance
  have hπUm : Irreducible (algebraMap S Um π) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← Algebra.FormallyUnramified.map_maximalIdeal (R := S) (S := Um),
      hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hyUm_unit : IsUnit (algebraMap U Um (AdjoinRoot.root (Pcf.Kummer.kummerPoly u e))) := by
    apply (isUnit_pow_iff he0).mp
    rw [← map_pow, Pcf.Kummer.root_kummerPoly_pow, ← IsScalarTower.algebraMap_apply]
    exact (u.map (algebraMap S Um : S →* Um)).isUnit
  set ϖ : Um := algebraMap S Um π * algebraMap U Um (AdjoinRoot.root (Pcf.Kummer.kummerPoly u e))
    with hϖdef
  have hϖ : Irreducible ϖ := (irreducible_mul_isUnit hyUm_unit).mpr hπUm
  -- The map `U_𝔪 → T`.
  have hψunit : ∀ s : m.primeCompl, IsUnit (ψ.toRingHom s) := fun s ↦ by
    have hs : (s : U) ∉ m := s.2
    rwa [Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal] at hs
  let ψ' : Um →+* T := IsLocalization.lift (M := m.primeCompl) hψunit
  have hψ'U : ∀ z : U, ψ' (algebraMap U Um z) = ψ z := fun z ↦ IsLocalization.lift_eq hψunit z
  have hψ'S : ∀ s : S, ψ' (algebraMap S Um s) = algebraMap S T s := fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S U Um, hψ'U, ψ.commutes]
  have hψ'ϖ : ψ' ϖ = algebraMap S T π * y := by
    rw [hϖdef, map_mul, hψ'S, hψ'U, hψroot]
  letI : Algebra Um T := ψ'.toAlgebra
  haveI : IsScalarTower S Um T := IsScalarTower.of_algebraMap_eq fun s ↦ (hψ'S s).symm
  -- (a) `ψ'` is a local homomorphism: `ϖ ↦ π y ∈ 𝔪_T`.
  have hϖT : ψ' ϖ ∈ maximalIdeal T := by
    rw [hψ'ϖ]
    exact Ideal.mul_mem_right _ _ hπ_mem
  haveI hψ'local : IsLocalHom ψ' := by
    constructor
    intro v hv
    by_contra hvu
    have hvm : v ∈ maximalIdeal Um := (mem_maximalIdeal v).mpr hvu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hvm
    obtain ⟨c, rfl⟩ := hvm
    rw [map_mul] at hv
    exact ((mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ hϖT)) hv
  -- Step 3: the `09EV` DVR `V = U_𝔪[z]/(zᵈ − ϖ)` and the local map `φ : V → T`, `z ↦ x`.
  let V := AdjoinRoot (dvrRootPoly ϖ d)
  letI : IsDomain V := dvrRootAlgebra_isDomain ϖ hd hϖ
  letI : IsDiscreteValuationRing V := dvrRootAlgebra_isDiscreteValuationRing ϖ hd hϖ
  have hVmax : maximalIdeal V = Ideal.span {AdjoinRoot.root (dvrRootPoly ϖ d)} :=
    (IsLocalRing.eq_maximalIdeal (dvrRootIdeal_isMaximal ϖ hd hϖ)).symm
  have hxV : (dvrRootPoly ϖ d).eval₂ (algebraMap Um T) x = 0 := by
    simp [dvrRootPoly, RingHom.algebraMap_toAlgebra, hψ'ϖ, hxy]
  let φ : V →ₐ[Um] T := AdjoinRoot.liftAlgHom _ (Algebra.ofId Um T) x hxV
  have hφroot : φ (AdjoinRoot.root _) = x := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hφmax : ∀ v : V, v ∈ maximalIdeal V → φ v ∈ maximalIdeal T := by
    intro v hv
    rw [hVmax, Ideal.mem_span_singleton'] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [map_mul, hφroot]
    exact Ideal.mul_mem_left _ _ hx_mem
  haveI : IsLocalHom φ.toRingHom := by
    constructor
    intro v hv
    by_contra hvu
    have hvm : v ∈ maximalIdeal V := (mem_maximalIdeal v).mpr hvu
    exact ((mem_maximalIdeal _).mp (hφmax v hvm)) hv
  -- Step 4: `φ` is surjective by dominance.
  have hroot_irred : Irreducible (AdjoinRoot.root (dvrRootPoly ϖ d)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hVmax
  have hsurj : Function.Surjective φ.toRingHom := by
    refine surjective_of_isLocalHom_of_dvr φ.toRingHom hroot_irred
      (by rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hφroot]) ?_
    intro t
    obtain ⟨p, q, hq, hpq⟩ := hgen t
    refine ⟨aeval (AdjoinRoot.root (dvrRootPoly ϖ d)) (p.map (algebraMap S Um)),
      aeval (AdjoinRoot.root (dvrRootPoly ϖ d)) (q.map (algebraMap S Um)), ?_, ?_⟩
    · change φ (aeval _ _) ≠ 0
      rwa [← Polynomial.aeval_algHom_apply, hφroot, Polynomial.aeval_map_algebraMap]
    · change φ (aeval _ _) * t = φ (aeval _ _)
      rwa [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hφroot,
        Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap]
  -- Uniformizer clause: `𝔪_T = φ(𝔪_V) = (x)`.
  have hmax : maximalIdeal T = Ideal.span {x} := by
    apply le_antisymm
    · intro t ht
      obtain ⟨v, rfl⟩ := hsurj t
      have hv : v ∈ maximalIdeal V := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hvu
        exact ((mem_maximalIdeal _).mp ht) (hvu.map φ.toRingHom)
      rw [hVmax, Ideal.mem_span_singleton'] at hv
      obtain ⟨c, rfl⟩ := hv
      rw [Ideal.mem_span_singleton']
      exact ⟨φ c, by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, hφroot]⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hx_mem
  refine ⟨hmax, ?_⟩
  -- Residue clause.
  -- (b) The induced `κ(S)`-algebra map `ψ̄ : κ(U_𝔪) → κ(T)`.
  let ψbar : ResidueField Um →ₐ[ResidueField S] ResidueField T :=
    { IsLocalRing.ResidueField.map ψ' with
      commutes' := fun k ↦ by
        obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective k
        change IsLocalRing.ResidueField.map ψ'
          (algebraMap (ResidueField S) (ResidueField Um) (residue S s)) =
          algebraMap (ResidueField S) (ResidueField T) (residue S s)
        rw [IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.map_residue,
          hψ'S, IsLocalRing.ResidueField.algebraMap_residue] }
  have hψbar : ∀ z : Um, ψbar (residue Um z) = residue T (ψ' z) := fun z ↦
    IsLocalRing.ResidueField.map_residue ψ' z
  -- (c) `ψ̄` is surjective: modulo `𝔪_T = (x)`, a polynomial in `x` over `U_𝔪` is its constant
  -- term.
  have hψbar_surj : Function.Surjective ψbar := by
    intro z
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨v, rfl⟩ := hsurj t
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective v
    refine ⟨residue Um (g.coeff 0), ?_⟩
    rw [hψbar]
    change residue T (ψ' (g.coeff 0)) = residue T (φ (AdjoinRoot.mk _ g))
    have hφg : φ (AdjoinRoot.mk _ g) = aeval x g := by
      rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, hφroot]
    rw [hφg]
    have hsub : aeval x g - ψ' (g.coeff 0) ∈ maximalIdeal T := by
      obtain ⟨h, hh⟩ := Polynomial.X_dvd_sub_C (p := g)
      have : aeval x g - ψ' (g.coeff 0) = x * aeval x h := by
        have h1 : aeval x (g - C (g.coeff 0)) = aeval x (X * h) := by rw [hh]
        rw [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X] at h1
        exact h1
      rw [this]
      exact Ideal.mul_mem_right _ _ hx_mem
    have := (IsLocalRing.residue_eq_zero_iff (aeval x g - ψ' (g.coeff 0))).mpr hsub
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  -- (e) Every element of `κ(T)` is the image of a separable element of `κ(U_𝔪)`.
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨w, rfl⟩ := hψbar_surj z
  exact IsSeparable.map ψbar ψbar.toRingHom.injective (Algebra.IsSeparable.isSeparable _ w)

/-- **Abhyankar's lemma for DVRs, divisibility form, uniformizer clause (Stacks Tag `0BRM`).**

Let `S` be a DVR with uniformizer `π`, `u ∈ Sˣ`, `e ≥ 1` invertible in `S`, `d ≥ 1`, and let `T`
be a DVR with a local `S`-algebra structure not killing `π`.  Let `x ∈ T` satisfy
`x ^ (d·e) = u·πᵉ` and suppose every element of `T` is a quotient of polynomials in `x` over `S`
(the fraction field of `T` is `Frac(S)(x)`).  Then `x` is a uniformizer of `T`.

In the notation of Tag `0BRM`: `S = B`, `πᵉu = π_A` is a uniformizer of `A`, `e ∣ E = d·e` is the
ramification index of `A ⊂ A₁ = A[π_A^{1/E}]`, and `T = (B₁)_𝔪`; the conclusion says that
`A₁ → T` has ramification index one.  This is the first clause of
`maximalIdeal_eq_span_root_of_dvd_and_isSeparable`. -/
@[stacks 0BRM "divisibility form e ∣ E with K₁ = K(π^{1/E}); conclusion: the root is a \
  uniformizer of (B₁)_𝔪 (ramification index one); tame case e ∈ Sˣ"]
theorem maximalIdeal_eq_span_root_of_dvd
    (π : S) (hπ : Irreducible π) (u : Sˣ) (e : ℕ) (he : 1 ≤ e) (heUnit : IsUnit (e : S))
    (d : ℕ) (hd : 1 ≤ d) (x : T)
    (hx : x ^ (d * e) = algebraMap S T ((u : S) * π ^ e))
    (hπ0 : algebraMap S T π ≠ 0)
    (hgen : ∀ t : T, ∃ p q : S[X], aeval x q ≠ 0 ∧ aeval x q * t = aeval x p) :
    maximalIdeal T = Ideal.span {x} :=
  (maximalIdeal_eq_span_root_of_dvd_and_isSeparable S T π hπ u e he heUnit d hd x hx hπ0 hgen).1

/-- **Abhyankar's lemma for DVRs, divisibility form (Stacks Tag `0BRM`).**

Let `R ⊂ S` be DVRs (Stacks' `A ⊂ B`), `a` a uniformizer of `R` with `a = u·πᵉ` in `S` (so `e` is
the ramification index), `e` invertible in `S`, and `E = d·e`.  Let `A₁ = R[x]/(xᴱ − a)` be the
`09EV` DVR, and let `T` be a DVR dominating `S` and receiving `A₁`, essentially of finite type over
`A₁` with separable residue extension, whose fraction field is generated over `Frac S` by the root
`x`.  Then `A₁ → T` is formally unramified.

In Stacks' notation `T = (B₁)_{𝔪ᵢⱼ}` for `K₁ = K(a^{1/E})`, and the conclusion "formally smooth in
the adic topology" is, for these essentially finite type local extensions, formal unramifiedness
(Stacks `0BRJ`). -/
@[stacks 0BRM "divisibility form e ∣ E with K₁ = K(π^{1/E}), tame case e ∈ Sˣ; (B₁)_𝔪 \
  replaced by any DVR dominating B with fraction field L(π^{1/E}); conclusion stated as \
  formal unramifiedness"]
theorem formallyUnramified_dvrRoot_of_dvd
    {R : Type w} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R S] [Algebra R T] [IsScalarTower R S T]
    (a : R) (ha : Irreducible a) (π : S) (hπ : Irreducible π) (u : Sˣ) (e : ℕ) (he : 1 ≤ e)
    (heUnit : IsUnit (e : S)) (hfactor : algebraMap R S a = (u : S) * π ^ e)
    (d : ℕ) (hd : 1 ≤ d)
    [Algebra (AdjoinRoot (dvrRootPoly a (d * e))) T]
    [IsScalarTower R (AdjoinRoot (dvrRootPoly a (d * e))) T]
    [Algebra.EssFiniteType (AdjoinRoot (dvrRootPoly a (d * e))) T]
    [Algebra.HasSeparableResidueFieldsAt (AdjoinRoot (dvrRootPoly a (d * e))) T
      ((maximalIdeal T).under (AdjoinRoot (dvrRootPoly a (d * e))))]
    (hπ0 : algebraMap S T π ≠ 0)
    (hgen : ∀ t : T, ∃ p q : S[X],
      aeval (algebraMap (AdjoinRoot (dvrRootPoly a (d * e))) T
        (AdjoinRoot.root (dvrRootPoly a (d * e)))) q ≠ 0 ∧
      aeval (algebraMap (AdjoinRoot (dvrRootPoly a (d * e))) T
        (AdjoinRoot.root (dvrRootPoly a (d * e)))) q * t =
      aeval (algebraMap (AdjoinRoot (dvrRootPoly a (d * e))) T
        (AdjoinRoot.root (dvrRootPoly a (d * e)))) p) :
    Algebra.FormallyUnramified (AdjoinRoot (dvrRootPoly a (d * e))) T := by
  have hE : 1 ≤ d * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  let A₁ := AdjoinRoot (dvrRootPoly a (d * e))
  letI : IsDomain A₁ := dvrRootAlgebra_isDomain a hE ha
  letI : IsLocalRing A₁ := dvrRootAlgebra_isLocalRing a hE ha
  set x : T := algebraMap A₁ T (AdjoinRoot.root (dvrRootPoly a (d * e))) with hxdef
  have hx : x ^ (d * e) = algebraMap S T ((u : S) * π ^ e) := by
    rw [hxdef, ← map_pow, dvrRoot_pow_eq, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S T, hfactor]
  have hmax : maximalIdeal T = Ideal.span {x} :=
    maximalIdeal_eq_span_root_of_dvd S T π hπ u e he heUnit d hd x hx hπ0 hgen
  have hx_mem : x ∈ maximalIdeal T := by
    rw [hmax]
    exact Ideal.subset_span (Set.mem_singleton x)
  -- the prime of `A₁` below `𝔪_T` is `(root)`
  set p : Ideal A₁ := (maximalIdeal T).under A₁ with hpdef
  have hp : p = Ideal.span {AdjoinRoot.root (dvrRootPoly a (d * e))} := by
    apply le_antisymm
    · rw [IsLocalRing.eq_maximalIdeal (dvrRootIdeal_isMaximal a hE ha)]
      exact IsLocalRing.le_maximalIdeal_of_isPrime p
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hx_mem
  haveI : (maximalIdeal T).LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p (maximalIdeal T)
  have hunr : Algebra.IsUnramifiedAt A₁ (maximalIdeal T) := by
    rw [Algebra.isUnramifiedAt_iff_map_eq A₁ p (maximalIdeal T)]
    refine ⟨Algebra.HasSeparableResidueFieldsAt.isSeparable (maximalIdeal T), ?_⟩
    rw [hp, Ideal.map_span, Set.image_singleton, IsScalarTower.algebraMap_apply A₁ T, ← hxdef,
      ← Set.image_singleton, ← Ideal.map_span, ← hmax]
    exact Localization.AtPrime.map_eq_maximalIdeal
  exact formallyUnramified_of_isUnramifiedAt_maximalIdeal A₁ T hunr

end Divisible

end Pcf.Stacks

#print axioms Pcf.Stacks.surjective_of_isLocalHom_of_dvr
#print axioms Pcf.Stacks.exists_unit_pow_eq_of_pow_mul_eq
#print axioms Pcf.Stacks.maximalIdeal_eq_span_root_of_dvd_and_isSeparable
#print axioms Pcf.Stacks.maximalIdeal_eq_span_root_of_dvd
#print axioms Pcf.Stacks.formallyUnramified_dvrRoot_of_dvd
