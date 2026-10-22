/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GaloisIntegralClosureInvariant
public import Pcf.Bounding.GeometricFibreBridge

/-!
# Factors of a Galois integral-closure fibre

The invariant action on the actual integral closure supplies the last
group-theoretic premise for the reduced tensor-fibre factor theorem.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x

set_option linter.style.haveILetI false

/-- The reduced tensor fibre of the actual integral closure of `R` in `L`. -/
abbrev GaloisIntegralClosureReducedFibre
    (R : Type u) (L : Type w) (F : Type x)
    [CommRing R] [Field L] [Field F]
    [Algebra R L] [Algebra R F] :=
  ((integralClosure R L ⊗[R] F) ⧸
    nilradical (integralClosure R L ⊗[R] F))

set_option maxHeartbeats 1000000 in
-- Elaborating the quotient field and its algebra structures needs a larger budget.
/-- A field factor of the actual reduced Galois integral-closure fibre
has prime-to-`p` monodromy over the centre field when the normalizing
Galois group has order prime to `p`. -/
theorem galoisIntegralClosure_fibreFactor_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (R : Type u) (K : Type v) (L : Type w) (F : Type x)
    [CommRing R] [IsDomain R] [Field K] [Field L] [Field F]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra R F] [IsIntegrallyClosed R]
    [FiniteDimensional K L] [IsGalois K L]
    [CharP R p] [CharP F p]
    [Module.Finite R (integralClosure R L)]
    (horder : (Fintype.card Gal(L/K)).Coprime p)
    (m : @MaximalSpectrum (GaloisIntegralClosureReducedFibre R L F)
      CommRing.toCommSemiring) :
    letI : Field (GaloisIntegralClosureReducedFibre R L F ⧸ m.asIdeal) := by
      exact Ideal.Quotient.field m.asIdeal
    IsPrimeToPMonodromy.{x, max w x, max w x} p F
      (GaloisIntegralClosureReducedFibre R L F ⧸ m.asIdeal) := by
  let B := integralClosure R L
  letI : IsFractionRing B L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction R K L B
  have hact := integralClosure_galois_action_invariant R K L
  letI : SMulCommClass Gal(L/K) R B := hact.1
  letI : Algebra.IsInvariant R B Gal(L/K) := hact.2
  exact tensorFibre_factor_primeToPMonodromy
    (R := R) (B := B) (F := F) (G := Gal(L/K)) p hp horder m

#print axioms galoisIntegralClosure_fibreFactor_primeToPMonodromy

end Pcf
