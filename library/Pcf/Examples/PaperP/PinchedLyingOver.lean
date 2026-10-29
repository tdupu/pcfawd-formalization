/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedLocalStructure

/-!
# Points of the pinched plane: rational points of `k[z, w]` and the fibre of `ν` over `o`

Helpers for `paper-p.tex`, Example `ex:pinched` and Remark `rem:pinched-unnormalized`.

* `le_of_X_sub_C_mem`: a prime `𝔮` of `k[z, w]` containing `z - a` and `w - b` contains every
  polynomial vanishing at `(a, b)`; so it is the maximal ideal of `(a, b)`
  (`eq_ker_of_X_sub_C_mem`).
* `nu_fibre_o`: the primes of `k[z, w]` over `o` are exactly `p₁` and `p₂`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedLyingOver

open AlgebraicGeometry MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedLocalStructure

set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k

omit [CharZero k] in
/-- A prime of `k[z, w]` containing `z - a` and `w - b` contains the kernel of evaluation at
`(a, b)`. -/
theorem le_of_X_sub_C_mem (a b : k) (Q : Ideal S) (h0 : X 0 - C a ∈ Q) (h1 : X 1 - C b ∈ Q) :
    RingHom.ker (aeval ![a, b] : S →ₐ[k] k).toRingHom ≤ Q := by
  have key : (Ideal.Quotient.mk Q) =
      (Ideal.Quotient.mk Q).comp ((C : k →+* S).comp (aeval ![a, b] : S →ₐ[k] k).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i
      fin_cases i
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, aeval_X]
        rw [Ideal.Quotient.eq]
        simpa using h0
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, aeval_X]
        rw [Ideal.Quotient.eq]
        simpa using h1
  intro s hs
  rw [RingHom.mem_ker] at hs
  rw [← Ideal.Quotient.eq_zero_iff_mem, key]
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [hs, map_zero, map_zero]

omit [CharZero k] in
/-- A proper ideal of `k[z, w]` containing `z - a` and `w - b` is the maximal ideal of
`(a, b)`. -/
theorem eq_ker_of_X_sub_C_mem (a b : k) (Q : Ideal S) (hQ : Q ≠ ⊤) (h0 : X 0 - C a ∈ Q)
    (h1 : X 1 - C b ∈ Q) :
    Q = RingHom.ker (aeval ![a, b] : S →ₐ[k] k).toRingHom :=
  ((RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, by simp⟩)).eq_of_le hQ
    (le_of_X_sub_C_mem k a b Q h0 h1)).symm

/-- **The fibre of `ν` over `o` is `{p₁, p₂}`.** -/
theorem nu_fibre_o (Q : Spec (.of S)) (hQ : PinchedAmbient.nu k Q = oPoint k) :
    Q = pOne k ∨ Q = pTwo k := by
  have hmem : ∀ h : R, h ∈ oIdeal k → PinchedRing.val k h ∈ Q.asIdeal := by
    intro h hh
    have : h ∈ (PinchedAmbient.nu k Q).asIdeal := by rw [hQ]; exact hh
    exact this
  have hw : (X 1 - 1 : S) ∈ Q.asIdeal := hmem _ (wSubOne_mem_oIdeal k)
  have hz : (X 0 - C 2) * (X 0 - C (-2)) ∈ Q.asIdeal := by
    have := hmem _ (zSqSubFour_mem_oIdeal k)
    convert this using 1
    change _ = (X 0 ^ 2 - 4 : S)
    simp only [map_neg, sub_neg_eq_add]
    have : (C 2 : S) = 2 := rfl
    rw [this]; ring
  have hw' : X 1 - C 1 ∈ Q.asIdeal := by simpa using hw
  rcases Q.isPrime.mem_or_mem hz with h | h
  · left
    apply PrimeSpectrum.ext
    exact eq_ker_of_X_sub_C_mem k 2 1 _ Q.isPrime.ne_top h hw'
  · right
    apply PrimeSpectrum.ext
    exact eq_ker_of_X_sub_C_mem k (-2) 1 _ Q.isPrime.ne_top h hw'

#print axioms le_of_X_sub_C_mem
#print axioms nu_fibre_o

end Pcf.Examples.PaperP.PinchedLyingOver
