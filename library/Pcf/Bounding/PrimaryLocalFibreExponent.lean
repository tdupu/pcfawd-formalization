/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryLocalExponentBound
public import Mathlib.RingTheory.Localization.Integral

/-!
# Fibre exponent for a DVR extension with fraction fields

Let `O ⊆ V` be a local inclusion of discrete valuation rings with fraction
fields `F ⊆ L`. Suppose `θ ∈ V` is a root of a monic `f ∈ F[X]` which, together
with a Bézout identity `a f + b f' = 1`, has coefficients in `O`, and suppose
that every `q`-th power in `L` lies in `F[θ]`. Then the `V`-valuation of a
uniformizer of `O` divides `q`.

This is the local form of `latex/paper-p.tex`, Lemma `lem:primary-fibres`: `F`
is the function field of a generic polynomial base, `F[θ]` the separable
closure of `F` in `L`, and `q` the exponent of `L` over it.
-/

@[expose] public section

namespace Pcf.Bounding

open IsDiscreteValuationRing Polynomial

variable {O V F L : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
  [IsLocalHom (algebraMap O V)]
  [Field F] [Field L] [Algebra O F] [IsFractionRing O F] [Algebra V L]
  [IsFractionRing V L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
  [IsScalarTower O V L]

/-- **Local fibre exponent.** Under the separable-part hypotheses above, the
`V`-valuation of a uniformizer `t` of `O` is a natural number dividing the
inseparable exponent `q`. -/
theorem addVal_dvd_of_separable_part
    (hinj : Function.Injective (algebraMap O V))
    {t : O} (ht : Irreducible t) (θ : V) (f a b : F[X]) (hf : f.Monic)
    (hfl : f ∈ lifts (algebraMap O F)) (hal : a ∈ lifts (algebraMap O F))
    (hbl : b ∈ lifts (algebraMap O F))
    (hcop : a * f + b * derivative f = 1)
    (hθ : aeval (algebraMap V L θ) f = 0)
    (q : ℕ) (hq : ∀ y : L, ∃ P : F[X], aeval (algebraMap V L θ) P = y ^ q) :
    ∃ e : ℕ, addVal V (algebraMap O V t) = e ∧ e ∣ q := by
  have hOF : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  have hVL : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  obtain ⟨fO, hfO, -, hmon⟩ := lifts_and_degree_eq_and_monic hfl hf
  obtain ⟨aO, haO⟩ := (mem_lifts a).mp hal
  obtain ⟨bO, hbO⟩ := (mem_lifts b).mp hbl
  have hcopO : IsCoprime fO (derivative fO) := by
    refine ⟨aO, bO, ?_⟩
    apply Polynomial.map_injective _ hOF
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, haO, hbO, hfO, hcop, Polynomial.map_one]
  have hθO : aeval θ fO = 0 := by
    apply hVL
    rw [map_zero, ← aeval_algebraMap_apply, ← aeval_map_algebraMap F, hfO, hθ]
  refine addVal_uniformizer_dvd_of_monogenic_unramified hinj ht fO hmon hcopO hθO q ?_
  intro v
  obtain ⟨P, hP⟩ := hq (algebraMap V L v)
  obtain ⟨d, hd, hN⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) P
  set N := IsLocalization.integerNormalization (nonZeroDivisors O) P
  have hkey : algebraMap O V d * v ^ q = aeval θ N := by
    apply hVL
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap F, hN, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O F L,
      ← hP]
    rw [show (d • P : F[X]) = C (algebraMap O F d) * P by
      rw [← smul_eq_C_mul, algebraMap_smul], map_mul, aeval_C]
  refine ⟨⟨aeval θ N, aeval_mem_adjoin_singleton O θ⟩,
    algebraMap O (Algebra.adjoin O ({θ} : Set V)) d, ?_, ?_⟩
  · intro h0
    have h := congrArg Subtype.val h0
    change algebraMap O V d = 0 at h
    rw [← map_zero (algebraMap O V)] at h
    exact nonZeroDivisors.ne_zero hd (hinj h)
  · exact hkey

#print axioms addVal_dvd_of_separable_part

end Pcf.Bounding
