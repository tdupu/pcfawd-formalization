/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Ramification of a DVR extension with bounded inseparable exponent

Let `A ⊆ V` be discrete valuation rings. If every `q`-th power of an element
of `V` lies in the fraction field of `A`, then the valuation in `V` of a
uniformizer of `A` divides `q`. In the proof of `latex/paper-p.tex`, Lemma
`lem:primary-fibres`, `q` is the exponent of the purely inseparable part of
the function-field extension, so the fibre multiplicity divides a fixed
power of `p`.
-/

@[expose] public section

namespace Pcf.Bounding

open IsDiscreteValuationRing

variable {A V : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra A V]

/-- If every `q`-th power of an element of `V` is a quotient of elements of
`A`, the `V`-valuation of a uniformizer of `A` is a natural number dividing
`q`. -/
theorem addVal_algebraMap_uniformizer_dvd
    (hinj : Function.Injective (algebraMap A V))
    {ϖ : A} (hϖ : Irreducible ϖ) (q : ℕ)
    (hpow : ∀ v : V, ∃ a b : A, b ≠ 0 ∧
      algebraMap A V b * v ^ q = algebraMap A V a) :
    ∃ e : ℕ, addVal V (algebraMap A V ϖ) = e ∧ e ∣ q := by
  have hϖ0 : algebraMap A V ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A V)]
    exact hinj.ne hϖ.ne_zero
  obtain ⟨e, he⟩ : ∃ e : ℕ, addVal V (algebraMap A V ϖ) = e :=
    ENat.ne_top_iff_exists.mp (by rwa [Ne, addVal_eq_top_iff]) |>.imp fun _ h => h.symm
  refine ⟨e, he, ?_⟩
  obtain ⟨π, hπ⟩ := exists_irreducible V
  obtain ⟨a, b, hb, hab⟩ := hpow π
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    have hb' : algebraMap A V b ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap A V)]
      exact hinj.ne hb
    exact (mul_ne_zero hb' (pow_ne_zero q hπ0)) hab
  obtain ⟨i, u, hu⟩ := eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨j, w, hw⟩ := eq_unit_mul_pow_irreducible hb hϖ
  have hval (c : Aˣ) (n : ℕ) :
      addVal V (algebraMap A V (c * ϖ ^ n)) = (n * e : ℕ) := by
    rw [map_mul, map_pow, addVal_mul, addVal_pow, he]
    have hc : addVal V (algebraMap A V c) = 0 :=
      addVal_eq_zero_of_unit ((Units.map (algebraMap A V).toMonoidHom) c)
    rw [hc, zero_add, nsmul_eq_mul]
    push_cast
    rfl
  have hsum := congrArg (addVal V) hab
  rw [addVal_mul, addVal_pow, addVal_uniformizer hπ, hu, hw, hval, hval] at hsum
  have hnat : j * e + q = i * e := by
    have : ((j * e + q : ℕ) : ℕ∞) = ((i * e : ℕ) : ℕ∞) := by
      rw [← hsum]
      push_cast
      simp
    exact_mod_cast this
  have hdvd : e ∣ j * e + q := hnat ▸ dvd_mul_left e i
  exact (Nat.dvd_add_right (dvd_mul_left e j)).mp hdvd

#print axioms addVal_algebraMap_uniformizer_dvd

end Pcf.Bounding
