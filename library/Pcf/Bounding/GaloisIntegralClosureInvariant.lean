/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Localization.Integral

/-!
# Galois invariants of an actual integral closure

For a finite Galois extension of the fraction field of a normal domain,
the Galois action restricts to the integral closure. Its fixed elements
are exactly the elements coming from the base domain.
-/

@[expose] public section

namespace Pcf

universe u v w

set_option linter.style.haveILetI false

/-- The actual integral closure of a normal domain in a finite Galois
extension carries the restricted Galois action, commuting with the base
action, and has precisely the base ring as invariant ring. -/
theorem integralClosure_galois_action_invariant
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsIntegrallyClosed R] [FiniteDimensional K L] [IsGalois K L] :
    let B := integralClosure R L
    letI : IsFractionRing B L :=
      integralClosure.isFractionRing_of_finite_extension K L
    letI : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction R K L B
    SMulCommClass Gal(L/K) R B ∧ Algebra.IsInvariant R B Gal(L/K) := by
  let B := integralClosure R L
  letI : IsFractionRing B L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction R K L B
  haveI : SMulCommClass Gal(L/K) R L := inferInstance
  haveI : SMulCommClass Gal(L/K) R B := ⟨by
    intro g r b
    apply (FaithfulSMul.algebraMap_injective B L)
    have hlin (x : B) : algebraMap B L (r • x) = r • algebraMap B L x := by
      simp only [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R B L]
    change algebraMap B L (galRestrict R K L B g (r • b)) =
      algebraMap B L (r • galRestrict R K L B g b)
    calc
      algebraMap B L (galRestrict R K L B g (r • b)) =
          g (algebraMap B L (r • b)) := algebraMap_galRestrict_apply R g (r • b)
      _ = g (r • algebraMap B L b) := by rw [hlin]
      _ = r • g (algebraMap B L b) := smul_comm g r (algebraMap B L b)
      _ = r • algebraMap B L (galRestrict R K L B g b) := by
        rw [algebraMap_galRestrict_apply]
      _ = algebraMap B L (r • galRestrict R K L B g b) := (hlin _).symm⟩
  constructor
  · infer_instance
  · exact Algebra.isInvariant_of_isGalois R K L B

#print axioms integralClosure_galois_action_invariant

end Pcf
