/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GeometricPrimeSpecialization

/-!
# Lying over for a prescribed centre in an intermediate normalization

If an intermediate coordinate algebra `S` embeds in a finite
normalization `B/R`, then `B/S` is integral. A prime defining a centre
in `S` therefore lies under a prime of `B`. The latter selects an
actual field component of the reduced tensor fibre.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.style.haveILetI false

universe u v w

variable {R : Type u} {S : Type v} {B : Type w}
  [CommRing R] [CommRing S] [CommRing B] [IsDomain B]
  [Algebra R S] [Algebra R B] [Module.Finite R B]

/-- A prime of an intermediate coordinate algebra lies under a prime
of the finite normalization, with the same contraction to `R`. -/
theorem exists_prime_of_finite_normalization_over_intermediate
    (ι : S →ₐ[R] B) (hι : Function.Injective ι)
    (Q : Ideal S) [Q.IsPrime] :
    ∃ q : Ideal B, q.IsPrime ∧
      q.comap ι.toRingHom = Q ∧
      q.under R = Q.under R := by
  letI : Algebra S B := ι.toRingHom.toAlgebra
  letI : IsScalarTower R S B :=
    IsScalarTower.of_algebraMap_eq (fun r => (ι.commutes r).symm)
  letI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  letI : Algebra.IsIntegral S B := Algebra.IsIntegral.tower_top R
  have hι' : Function.Injective (algebraMap S B) := hι
  have hker : RingHom.ker (algebraMap S B) ≤ Q := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hι']
    exact bot_le
  obtain ⟨q, hqprime, hqover⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain Q hker
  refine ⟨q, hqprime, ?_, ?_⟩
  · exact hqover
  · calc
      q.under R = (q.under S).under R :=
        (Ideal.under_under (A := R) (B := S) (C := B)
          q).symm
      _ = Q.under R := congrArg (fun I : Ideal S => I.under R) hqover

/-- The prescribed prime of `S` is the contraction of an actual
field factor of the reduced fibre above its image in `R`. -/
theorem exists_tensorFibre_factor_over_intermediate_prime
    (ι : S →ₐ[R] B) (hι : Function.Injective ι)
    (Q : Ideal S) [Q.IsPrime] :
    ∃ m : MaximalSpectrum
      ((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))),
      RingHom.ker
        (tensorFibreComponentMap (F := FractionRing (R ⧸ Q.under R)) ι m) = Q := by
  obtain ⟨q, hqprime, hqS, hqR⟩ :=
    exists_prime_of_finite_normalization_over_intermediate ι hι Q
  letI : q.IsPrime := hqprime
  letI : q.LiesOver (Q.under R) := ⟨hqR.symm⟩
  obtain ⟨m, hm⟩ :=
    exists_tensorFibre_factor_over_prime ι (Q.under R) q
  exact ⟨m, hm.trans hqS⟩

#print axioms exists_prime_of_finite_normalization_over_intermediate
#print axioms exists_tensorFibre_factor_over_intermediate_prime

end Pcf
