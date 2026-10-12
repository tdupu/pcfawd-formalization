/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Abhyankar
import Pcf.Stacks.Abhyankar.DVRAbhyankar

/-!
# The root-of-a-unit leg in the DVR Abhyankar square

In the last paragraph of Stacks Tag `0BRM`, after adjoining the ramified root on the base,
the other leg is obtained by adjoining an `e`th root of a unit.  That Kummer algebra is etale
when `e` is invertible.  A chosen finite local factor is therefore etale as well, and the
ramification-square theorem applies.

This file makes that implication explicit.  Its localization equivalence is the actual output
of choosing a prime of the Kummer algebra; it does not assume etaleness of the desired leg.
-/

open IsLocalRing

universe u v w x

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- A finite algebra identified with a local factor of a root-of-a-unit Kummer algebra is
etale over the base DVR.

The finite-module hypothesis turns the formally etale localized Kummer algebra into a finitely
presented algebra after transport across the displayed equivalence. -/
theorem etale_of_equiv_localization_kummerUnit
    (S : Type v) (T : Type x) [CommRing S] [CommRing T] [Algebra S T]
    [IsNoetherianRing S] [Module.Finite S T]
    (unit : Sˣ) (e : ℕ) (he : e ≠ 0) (heUnit : IsUnit (e : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit e))) [q.IsPrime]
    (equiv : T ≃ₐ[S] Localization.AtPrime q) :
    Algebra.Etale S T := by
  let U := AdjoinRoot (Abhyankar.kummerPoly unit e)
  letI : Algebra.Etale S U := Abhyankar.etale unit he heUnit
  letI : Algebra.FormallyEtale S (Localization.AtPrime q) := inferInstance
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_equiv equiv.symm
  letI : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- The root-of-a-unit specialization of the final ramification square in Tag `0BRM`.

The lower extensions `S/R` and `A/R` have the same ramification index.  The chosen top ring
`T` is a finite local factor of the Kummer algebra obtained from `S` by adjoining an `e`th
root of a unit.  The preceding theorem proves that auxiliary leg etale, after which
`etale_of_dvr_ramification_square` proves that `A → T` is finite etale. -/
theorem etale_of_dvr_kummerUnit_ramification_square
    (R : Type u) (S : Type v) (A : Type w) (T : Type x)
    [CommRing R] [CommRing S] [CommRing A] [CommRing T]
    [IsDomain R] [IsDomain S] [IsDomain A] [IsDomain T]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R A] [Algebra R T] [Algebra S T] [Algebra A T]
    [IsScalarTower R S T] [IsScalarTower R A T]
    [Module.Finite R S] [Module.Finite R A] [Module.Finite S T] [Module.Finite A T]
    [FaithfulSMul A T]
    [IsLocalHom (algebraMap S T)] [IsLocalHom (algebraMap A T)]
    [Algebra.HasSeparableResidueFieldsAt A T ((maximalIdeal T).under A)]
    (unit : Sˣ) (e : ℕ) (he : e ≠ 0) (heUnit : IsUnit (e : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit e))) [q.IsPrime]
    (equiv : T ≃ₐ[S] Localization.AtPrime q)
    (hindex : (maximalIdeal S).ramificationIdx R =
      (maximalIdeal A).ramificationIdx R) :
    Algebra.Etale A T := by
  letI : Algebra.Etale S T :=
    etale_of_equiv_localization_kummerUnit S T unit e he heUnit q equiv
  exact etale_of_dvr_ramification_square R S A T hindex

#print axioms etale_of_equiv_localization_kummerUnit
#print axioms etale_of_dvr_kummerUnit_ramification_square

end Pcf.Stacks
