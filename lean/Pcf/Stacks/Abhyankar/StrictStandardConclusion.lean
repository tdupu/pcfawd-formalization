/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationStandardDescent
public import Pcf.Stacks.Common.EtaleRegular
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# From a strict-local presentation to the Abhyankar conclusion

This is the terminal bookkeeping in the descent paragraph of Stacks Tag `0EYG`.  Once the
normalization after strict henselization has been identified with a finite disjoint union of
standard tame covers, coherent `05N9` descent supplies one pointed etale stage.  The theorem
below packages that stage as the exact manuscript-facing conclusion.
-/

@[expose] public section

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

open TensorProduct

set_option linter.style.haveILetI false

/-- A strict-local standard-cover presentation descends to the exact local standard-cover
conclusion.  The equality on the kernel of the chosen geometric point is the literal assertion
that the pointed etale neighbourhood lies over `y`; it is structural input, not an etaleness or
standard-cover hypothesis. -/
theorem hasAbhyankarStandardCoverAt_of_strict
    {R Ω S : Type u} [CommRing R] [Field Ω] [CommRing S]
    [Algebra R Ω] [Algebra R S] [IsNoetherianRing R]
    (a : R) (y : PrimeSpectrum R)
    (hΩ : RingHom.ker (algebraMap R Ω) = y.asIdeal)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [Module.Finite R S]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (hstrict : IsFiniteDisjointUnionOfStandardTameCovers
      (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S)
      (algebraMap R (LocalColimit R Ω) a)) :
    HasAbhyankarStandardCoverAt R S a y := by
  obtain ⟨X, hstandard⟩ :=
    exists_pointedEtale_standardTameCover_of_strict a hnat hstrict
  let y' : PrimeSpectrum X :=
    ⟨RingHom.ker X.point.toRingHom, RingHom.ker_isPrime X.point.toRingHom⟩
  have hy' : y'.asIdeal.under R = y.asIdeal := by
    change (RingHom.ker X.point.toRingHom).under R = y.asIdeal
    rw [← hΩ]
    ext r
    simp only [Ideal.mem_under, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, X.point.commutes]
  let _ : IsNoetherianRing X := Algebra.FiniteType.isNoetherianRing R X
  have hmapRegular : algebraMap R X a ∈ nonZeroDivisors X := by
    letI : SMul R X := Algebra.toSMul
    letI : Module R X := Algebra.toModule
    letI : Module.Flat R X := Algebra.Smooth.flat R X
    have hsmul : IsSMulRegular X a :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors ha
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      apply hsmul
      simpa only [Algebra.smul_def, mul_zero] using hx
    · intro x hx
      apply hsmul
      simpa only [Algebra.smul_def, mul_zero, zero_mul, mul_comm] using hx
  let _ : IsRegularRing (X ⧸ Ideal.span ({algebraMap R X a} : Set X)) :=
    quotient_span_isRegularRing_of_etale R X a
  refine ⟨X, inferInstance, inferInstance, inferInstance, ?_, inferInstance,
    hmapRegular, inferInstance, hstandard⟩
  exact ⟨y', hy'⟩

#print axioms hasAbhyankarStandardCoverAt_of_strict

end Pcf.Stacks.PointedEtaleNeighborhood
