/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictRootCover
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Etale.Basic

/-!
# The exponent of a standard tame piece is a unit (Stacks Tag `0EYG`, last paragraph)

The last three sentences of the proof of Stacks Tag `0EYG` (Lemma 58.31.5):

> However, the ramification locus of the ring map `A_f → A_f[y]/(y^n − f)` is cut out by
> `n y^{n−1}` which must imply that `n` is a unit in `A_f`.  Since `f` is a prime element, this
> means that `n = u f^s` for some unit `u` of `A` and `s ∈ ℤ`.  Since `n` maps to a unit in
> `κ(𝔭)` we find `s = 0` and the proof is complete.

This file proves that statement for a component `N ≅ A[x]/(x^n − a)` of the normalization over a
Noetherian local ring `A` with regular divisor `a`: if `N[1/a]` is étale over `A` and `n ∉ (a)`,
then `n` is a unit of `A`.  In the tame form of Abhyankar's lemma the hypothesis `n ∉ (a)` comes
from the tameness in codimension one (the ramification index `n` of the component at the prime
over `(a)` is a unit in `κ((a))`), and the conclusion is the clause "`e` is invertible in `A`"
of the standard tamely ramified morphism (Stacks Tag `0EYF`).

## Stacks proof step → Lean lemma

* "the ramification locus … is cut out by `n y^{n−1}`, so `n` is a unit in `A_f`" →
  `isUnit_natCast_localizationAway_of_etale`, Step 1
* "since `f` is prime, `n = u f^s`" → Step 2 of `isUnit_natCast_of_strictRootCover_etale_away`
  (constant coordinate of `n m = a^k` in the power basis) and `isUnit_of_mul_eq_pow_of_not_dvd`
* "since `n` maps to a unit in `κ(𝔭)`, `s = 0`" → hypothesis `hna : (n : A) ∉ (a)` fed to
  `isUnit_of_mul_eq_pow_of_not_dvd`

## Divergence from Stacks

Stacks reads off `n ∈ A_f^×` from the ramification locus `V(n y^{n−1})` of the standard étale
presentation.  Here unramifiedness of `N[1/a]` over `A` is applied directly: the two `A`-algebra
maps `N[1/a] → M[ε]`, `M = N[1/a]/(n)`, `ε² = 0`, given by `y ↦ ȳ` and `y ↦ ȳ + ε` agree modulo
the square-zero ideal `(ε)`, hence are equal, which forces `1 = 0` in `M`.  This is the statement
`Ω_{N[1/a]/A} = N[1/a]/(n y^{n−1}) = 0` unwound on the universal first-order deformation, with the
unit `y` already absorbed.  The arithmetic "`n = u f^s`" is carried out on the constant coordinate
of the power basis `1, x, …, x^{n−1}` of `A[x]/(x^n − a)` instead of in the fraction field.
-/

@[expose] public section

universe u

open IsLocalRing Polynomial TrivSqZeroExt

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section PrimePower

/-- **"`n = u f^s` … we find `s = 0`."**  In a domain, if `x c = b^k` with `b` a prime element not
dividing `x`, then `x` is a unit: `b` divides `c` repeatedly, and after cancelling `b^k` one is
left with `x c' = 1`. -/
theorem isUnit_of_mul_eq_pow_of_not_dvd {A : Type*} [CommRing A] [IsDomain A] {b x : A}
    (hb : Prime b) (hx : ¬ b ∣ x) : ∀ (k : ℕ) (c : A), x * c = b ^ k → IsUnit x
  | 0, c, h => IsUnit.of_mul_eq_one c (by simpa using h)
  | k + 1, c, h => by
    have hdvd : b ∣ x * c := ⟨b ^ k, by rw [h, pow_succ, mul_comm]⟩
    rcases hb.dvd_or_dvd hdvd with hbx | ⟨c', rfl⟩
    · exact absurd hbx hx
    · apply isUnit_of_mul_eq_pow_of_not_dvd hb hx k c'
      have hcancel : b * (x * c') = b * b ^ k := by
        rw [← pow_succ', ← h]
        ring
      exact mul_left_cancel₀ hb.ne_zero hcancel

end PrimePower

section Unramified

variable {A : Type u} [CommRing A] (a : A) {n : ℕ}

/-- **"The ramification locus of `A_f → A_f[y]/(y^n − f)` is cut out by `n y^{n−1}`, which must
imply that `n` is a unit in `A_f`."**

Let `N ≅ A[x]/(x^n − a)` be an `A`-algebra with `N[1/a]` formally unramified over `A`.  Then `n`
is a unit of `N[1/a]`.

Proof (divergence from Stacks, see the module docstring): let `M = N[1/a]/(n)` and `B = M[ε]`
(`TrivSqZeroExt M M`).  The `A`-algebra maps `g₁, g₂ : N[1/a] → B` with `g₁(x) = x̄`,
`g₂(x) = x̄ + ε` are well defined (`(x̄ + ε)^n = x̄^n + n x̄^{n−1} ε = ā` since `n = 0` in `M`) and
agree modulo the square-zero ideal `ker(B → M) = (ε)`; formal unramifiedness forces `g₁ = g₂`,
so `ε = 0`, so `1 = 0` in `M`, i.e. `(n) = N[1/a]`. -/
theorem isUnit_natCast_localizationAway_of_etale
    (N : Type u) [CommRing N] [Algebra A N] (e : N ≃ₐ[A] StrictRootCover a n)
    [Algebra.FormallyUnramified A (Localization.Away (algebraMap A N a))] :
    IsUnit ((n : ℕ) : Localization.Away (algebraMap A N a)) := by
  let Na := Localization.Away (algebraMap A N a)
  let I : Ideal Na := Ideal.span {((n : ℕ) : Na)}
  let M := Na ⧸ I
  let B := TrivSqZeroExt M M
  -- the root of `N` and its class in `M`
  let xN : N := e.symm (strictRoot a n)
  have hxN : xN ^ n = algebraMap A N a := by
    rw [← map_pow, strictRoot_pow, AlgEquiv.commutes]
  let xbar : M := Ideal.Quotient.mk I (algebraMap N Na xN)
  have hnM : ((n : ℕ) : M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hxbar : xbar ^ n = algebraMap A M a := by
    rw [← map_pow, ← map_pow, hxN, ← IsScalarTower.algebraMap_apply A N Na,
      Ideal.Quotient.mk_algebraMap]
  -- the first-order deformation `x̄ + ε`
  let ξ : B := inl xbar + inr 1
  have hξfst : ξ.fst = xbar := by rw [fst_add, fst_inl, fst_inr, add_zero]
  have hξsnd : ξ.snd = 1 := by rw [snd_add, snd_inl, snd_inr, zero_add]
  have hξpow : ξ ^ n = inl (xbar ^ n) := by
    apply TrivSqZeroExt.ext
    · rw [fst_pow, hξfst, fst_inl]
    · rw [snd_pow, hξfst, hξsnd, snd_inl, smul_eq_mul, mul_one, nsmul_eq_mul, hnM, zero_mul]
  have hξroot : (Pcf.LocalModel.localPoly (1 : Aˣ) a n).eval₂ (Algebra.ofId A B) ξ = 0 := by
    simp only [Pcf.LocalModel.localPoly, eval₂_sub, eval₂_X_pow, eval₂_C, Units.val_one, one_mul,
      hξpow, hxbar]
    rw [sub_eq_zero]
    rfl
  -- the two `A`-algebra maps `N[1/a] → B`
  let g₁ : Na →ₐ[A] B := (inlAlgHom A M M).comp (Ideal.Quotient.mkₐ A I)
  let g₂' : StrictRootCover a n →ₐ[A] B :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId A B) ξ hξroot
  have hg₂'root : g₂' (strictRoot a n) = ξ := AdjoinRoot.liftAlgHom_root _ _ _ _
  let f₂ : N →ₐ[A] B := g₂'.comp e.toAlgHom
  have hf₂unit : ∀ y : Submonoid.powers (algebraMap A N a), IsUnit (f₂ y) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
    change IsUnit (f₂ (algebraMap A N a ^ k))
    rw [map_pow, f₂.commutes, TrivSqZeroExt.algebraMap_eq_inl']
    apply IsUnit.pow
    rw [isUnit_inl_iff, IsScalarTower.algebraMap_apply A Na M,
      IsScalarTower.algebraMap_apply A N Na]
    exact (IsLocalization.Away.algebraMap_isUnit (algebraMap A N a)).map (algebraMap Na M)
  let g₂ : Na →ₐ[A] B :=
    IsLocalization.liftAlgHom (A := A) (R := N) (M := Submonoid.powers (algebraMap A N a))
      (S := Na) (P := B) (f := f₂) hf₂unit
  have hg₂ : ∀ y : N, g₂ (algebraMap N Na y) = f₂ y := fun y ↦
    IsLocalization.lift_eq hf₂unit y
  -- they agree after projecting to `M`
  have hfst : (fstHom A M M).comp g₁ = (fstHom A M M).comp g₂ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (algebraMap A N a))
    have hext : ∀ φ ψ : N →ₐ[A] M, φ.comp e.symm.toAlgHom = ψ.comp e.symm.toAlgHom → φ = ψ := by
      intro φ ψ h
      ext y
      have := AlgHom.congr_fun h (e y)
      simpa using this
    apply hext
    apply AdjoinRoot.algHom_ext
    change (fstHom A M M) (g₁ (algebraMap N Na (e.symm (strictRoot a n)))) =
      (fstHom A M M) (g₂ (algebraMap N Na (e.symm (strictRoot a n))))
    rw [hg₂]
    change (inl xbar : B).fst = (g₂' (e (e.symm (strictRoot a n)))).fst
    rw [AlgEquiv.apply_symm_apply, hg₂'root, fst_inl, hξfst]
  -- the kernel of the projection is square zero
  let π : B →+* M :=
    { toFun := TrivSqZeroExt.fst
      map_one' := fst_one
      map_mul' := fst_mul
      map_zero' := fst_zero (M := M)
      map_add' := fst_add }
  let J : Ideal B := RingHom.ker π
  have hJ : ∀ z ∈ J, z = inr z.snd := by
    intro z hz
    have hz' : z.fst = 0 := hz
    exact TrivSqZeroExt.ext (by rw [hz', fst_inr]) (by rw [snd_inr])
  have hJsq : J * J = ⊥ := by
    rw [eq_bot_iff]
    refine Ideal.mul_le.mpr fun r hr s hs ↦ ?_
    rw [Ideal.mem_bot, hJ r hr, hJ s hs, inr_mul_inr]
  have hJnil : IsNilpotent J := by
    refine ⟨2, ?_⟩
    rw [Submodule.pow_succ, Submodule.pow_one, Ideal.zero_eq_bot]
    exact hJsq
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext (R := A) (A := Na) (B := B) J hJnil
      (g₁ := g₁) (g₂ := g₂) fun z ↦ ?_
    rw [Ideal.Quotient.eq]
    change (g₁ z - g₂ z).fst = 0
    rw [fst_sub, sub_eq_zero]
    exact AlgHom.congr_fun hfst z
  -- evaluate at the root: `inl x̄ = inl x̄ + inr 1`
  have hval : g₁ (algebraMap N Na xN) = g₂ (algebraMap N Na xN) := by rw [hg]
  rw [hg₂] at hval
  change (inl xbar : B) = g₂' (e (e.symm (strictRoot a n))) at hval
  rw [AlgEquiv.apply_symm_apply, hg₂'root] at hval
  have hone : (1 : M) = 0 := by
    have := congrArg TrivSqZeroExt.snd hval
    rw [snd_inl, snd_add, snd_inl, snd_inr, zero_add] at this
    exact this.symm
  have hItop : I = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hone
  exact Ideal.span_singleton_eq_top.mp hItop

end Unramified

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : A)

/-- **The exponent of a standard tame piece is a unit (Stacks Tag `0EYG`, last paragraph).**

Let `A` be a Noetherian local ring, `a ∈ 𝔪_A` a nonzerodivisor with `A ⧸ (a)` regular local, and
`N ≅ A[x]/(x^n − a)` an `A`-algebra (`n ≥ 1`) with `N[1/a]` étale over `A`.  If `n ∉ (a)` (in the
proof of `0EYG`: "`n` maps to a unit in `κ(𝔭)`", the tameness of the component), then `n` is a
unit of `A`.

Stacks proof step → Lean:
* "the ramification locus of `A_f → A_f[y]/(y^n − f)` is cut out by `n y^{n−1}` which must imply
  that `n` is a unit in `A_f`": Step 1, `isUnit_natCast_localizationAway_of_etale`;
* "Since `f` is a prime element, this means that `n = u f^s` for some unit `u` of `A`": Step 2,
  from `n ∈ N[1/a]^×` one gets `n m = a^k` in `N`, and the constant coordinate in the power basis
  `1, x, …, x^{n−1}` gives `n c₀ = a^k` in `A`;
* "Since `n` maps to a unit in `κ(𝔭)` we find `s = 0`": Step 3,
  `isUnit_of_mul_eq_pow_of_not_dvd` with the prime element `a` and `a ∤ n`.

Divergence from Stacks: see the module docstring (unramifiedness is applied to the first-order
deformation `x ↦ x̄ + ε` instead of reading off the ramification locus; the factorisation
`n = u f^s` is done on the constant coordinate of the power basis instead of in `A_f`). -/
theorem isUnit_natCast_of_strictRootCover_etale_away
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] {n : ℕ} (hn : 1 ≤ n)
    (hna : ((n : ℕ) : A) ∉ Ideal.span ({a} : Set A))
    (N : Type u) [CommRing N] [Algebra A N] (e : N ≃ₐ[A] StrictRootCover a n)
    [Algebra.Etale A (Localization.Away (algebraMap A N a))] :
    IsUnit ((n : ℕ) : A) := by
  haveI : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha ha0
  haveI : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  have ha0' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  haveI hp : (Ideal.span ({a} : Set A)).IsPrime := divisorPrime_isPrime a
  have hprime : Prime a := (Ideal.span_singleton_prime ha0').mp hp
  have hndvd : ¬ a ∣ ((n : ℕ) : A) := fun h ↦ hna (Ideal.mem_span_singleton.mpr h)
  let Na := Localization.Away (algebraMap A N a)
  -- Step 1: `n` is a unit of `N[1/a]`.
  have hunit : IsUnit ((n : ℕ) : Na) := isUnit_natCast_localizationAway_of_etale a N e
  -- Step 2: `n m = a ^ k` in `N`, then `n c₀ = a ^ k` in `A`.
  obtain ⟨c, hc⟩ := hunit.exists_right_inv
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A N a)) c
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have haN : algebraMap A N a ∈ nonZeroDivisors N := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    apply e.injective
    rw [map_zero]
    have hx : strictRoot a n ^ n ∈ nonZeroDivisors (StrictRootCover a n) :=
      pow_mem (strictRoot_mem_nonZeroDivisors a hn ha0) n
    have hmul : e y * strictRoot a n ^ n = 0 := by
      rw [strictRoot_pow, ← e.commutes a, ← map_mul, hy, map_zero]
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hx).mp hmul
  have hinj : Function.Injective (algebraMap N Na) :=
    IsLocalization.injective Na (Submonoid.powers_le.mpr haN)
  have hmN : ((n : ℕ) : N) * m = algebraMap A N a ^ k := by
    apply hinj
    simp only at hs
    rw [map_mul, map_natCast, map_pow, ← hs, ← mul_assoc, hc, one_mul, ← map_pow, hk]
  let A' := StrictRootCover a n
  have hmA' : ((n : ℕ) : A') * e m = algebraMap A A' (a ^ k) := by
    have := congrArg e hmN
    rwa [map_mul, map_natCast, map_pow, AlgEquiv.commutes, ← map_pow] at this
  -- the constant coordinate in the power basis `1, x, …, x^{n-1}`
  let pb : PowerBasis A A' := AdjoinRoot.powerBasis' (Pcf.LocalModel.localPoly_monic 1 a hn)
  have hdim : 0 < pb.dim := by
    change 0 < (Pcf.LocalModel.localPoly (1 : Aˣ) a n).natDegree
    rw [Pcf.LocalModel.localPoly_natDegree]
    omega
  let i0 : Fin pb.dim := ⟨0, hdim⟩
  have hb0 : pb.basis i0 = 1 := by
    rw [PowerBasis.basis_eq_pow]
    exact pow_zero _
  have hrepr_alg : ∀ r : A, pb.basis.repr (algebraMap A A' r) i0 = r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, ← hb0, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have hrepr_mul : ∀ y : A', pb.basis.repr (((n : ℕ) : A') * y) i0 =
      ((n : ℕ) : A) * pb.basis.repr y i0 := by
    intro y
    rw [← map_natCast (algebraMap A A'), ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      smul_eq_mul]
  have hc₀ : ((n : ℕ) : A) * pb.basis.repr (e m) i0 = a ^ k := by
    rw [← hrepr_mul, hmA', hrepr_alg]
  -- Step 3: `a` is prime and `a ∤ n`, so `n` is a unit.
  exact isUnit_of_mul_eq_pow_of_not_dvd hprime hndvd k _ hc₀

end Main

end Pcf.Stacks

