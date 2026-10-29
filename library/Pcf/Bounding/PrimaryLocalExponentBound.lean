/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryDVRExponentDivides
public import Pcf.Bounding.PrimaryAdjoinRootUnramified
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Local exponent bound for a DVR over a monogenic unramified part

Let `O ⊆ V` be a local inclusion of discrete valuation rings, and let
`θ ∈ V` be a root of a monic polynomial over `O` coprime to its
derivative. If every `q`-th power of an element of `V` is a quotient of
elements of `O[θ]`, then the `V`-valuation of a uniformizer `t` of `O`
divides `q`.

In the proof of `latex/paper-p.tex`, Lemma `lem:primary-fibres`, `O` is the
local ring of the base at a Gauss prime, `O[θ]` is the generically separable
part of the function field, and `q` is the exponent of the purely
inseparable remainder.
-/

@[expose] public section

namespace Pcf.Bounding

open IsLocalRing IsDiscreteValuationRing Polynomial

variable {O V : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
  [IsLocalHom (algebraMap O V)]

/-- **Local exponent bound.** The valuation of a uniformizer of `O` in `V`
divides the exponent `q` of the extension over the unramified monogenic part
`O[θ]`. -/
theorem addVal_uniformizer_dvd_of_monogenic_unramified
    (hinj : Function.Injective (algebraMap O V))
    {t : O} (ht : Irreducible t) (f : O[X]) (hf : f.Monic)
    (hcop : IsCoprime f (derivative f)) {θ : V} (hθ : aeval θ f = 0) (q : ℕ)
    (hpow : ∀ v : V, ∃ a b : Algebra.adjoin O ({θ} : Set V), b ≠ 0 ∧
      (b : V) * v ^ q = a) :
    ∃ e : ℕ, addVal V (algebraMap O V t) = e ∧ e ∣ q := by
  let S := Algebra.adjoin O ({θ} : Set V)
  have : FaithfulSMul O V := (faithfulSMul_iff_algebraMap_injective O V).mpr hinj
  let φ : S →+* V := (S.val : S →ₐ[O] V).toRingHom
  have hφinj : Function.Injective φ := Subtype.val_injective
  let P : Ideal S := (maximalIdeal V).comap φ
  have hPprime : P.IsPrime := Ideal.comap_isPrime φ (maximalIdeal V)
  have hPover : P.LiesOver (maximalIdeal O) := by
    constructor
    change maximalIdeal O = ((maximalIdeal V).comap φ).comap (algebraMap O S)
    rw [Ideal.comap_comap]
    have hcomp : φ.comp (algebraMap O S) = algebraMap O V := by
      ext x
      rfl
    rw [hcomp, IsLocalRing.maximalIdeal_comap]
  have hKD := adjoin_map_eq_maximalIdeal_of_isCoprime_derivative f hf hcop hθ
    (maximalIdeal O) P
  let A := Localization.AtPrime P
  have : Module.Finite O S :=
    Algebra.finite_adjoin_simple_of_isIntegral ⟨f, hf, by rwa [← aeval_def]⟩
  have : IsNoetherianRing S := IsNoetherianRing.of_finite O S
  have hSA : Function.Injective (algebraMap S A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  have hOS : Function.Injective (algebraMap O S) := by
    intro x y hxy
    apply hinj
    exact congrArg φ hxy
  have hmax : maximalIdeal A = Ideal.span {algebraMap O A t} := by
    rw [← hKD, ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hOA : Function.Injective (algebraMap O A) := by
    rw [IsScalarTower.algebraMap_eq O S A]
    exact hSA.comp hOS
  have ht0 : algebraMap O A t ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O A)]
    exact hOA.ne ht.ne_zero
  have hnotfield : ¬IsField A := by
    rw [isField_iff_maximalIdeal_eq, hmax]
    exact fun h => ht0 (Ideal.span_singleton_eq_bot.mp h)
  have : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnotfield).out 1 5).mpr
      (show (maximalIdeal A).IsPrincipal from ⟨⟨_, hmax⟩⟩)
  have hirrA : Irreducible (algebraMap O A t) :=
    irreducible_of_span_eq_maximalIdeal _ ht0 hmax
  have hunit : ∀ s : P.primeCompl, IsUnit (φ s) := by
    intro s
    by_contra hs
    exact s.2 hs
  let ψ : A →+* V := IsLocalization.lift (M := P.primeCompl) hunit
  have hψ (s : S) : ψ (algebraMap S A s) = φ s := IsLocalization.lift_eq _ _
  have hψinj : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    exact ⟨fun h => by rw [hSA h], fun h => by rw [hφinj h]⟩
  let _ : Algebra A V := ψ.toAlgebra
  obtain ⟨e, he, hdvd⟩ := addVal_algebraMap_uniformizer_dvd hψinj hirrA q (by
    intro v
    obtain ⟨a, b, hb, hab⟩ := hpow v
    refine ⟨algebraMap S A a, algebraMap S A b, ?_, ?_⟩
    · rw [Ne, ← map_zero (algebraMap S A)]
      exact hSA.ne hb
    · change ψ (algebraMap S A b) * v ^ q = ψ (algebraMap S A a)
      rw [hψ, hψ]
      exact hab)
  refine ⟨e, ?_, hdvd⟩
  have hmap : algebraMap A V (algebraMap O A t) = algebraMap O V t := by
    change ψ (algebraMap O A t) = algebraMap O V t
    rw [IsScalarTower.algebraMap_apply O S A, hψ]
    rfl
  rw [← hmap]
  exact he

#print axioms addVal_uniformizer_dvd_of_monogenic_unramified

end Pcf.Bounding
