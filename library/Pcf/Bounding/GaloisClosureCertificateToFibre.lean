/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PrimeToPMonodromy
public import Pcf.Bounding.GaloisIntegralClosureFactor
public import Pcf.Stacks.Purity.IntegralClosure

/-!
# A prime-to-`p` closure certificate for a geometric fibre

The normal closure selected by a monodromy certificate is an actual
finite Galois field extension. Its Galois group has order prime to `p`,
which is the group-order input of the integral-closure fibre theorem.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x z

set_option linter.style.haveILetI false

/-- Choose the finite normal closure recorded by a prime-to-`p`
monodromy proof. -/
noncomputable def chosenPrimeToPMonodromyCertificate
    (p : ℕ) (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E]
    (hmono : IsPrimeToPMonodromy.{u, v, w} p K E) :
    PrimeToPMonodromyCertificate.{u, v, w} p K E :=
  Classical.choice hmono

/-- The actual field chosen as normal closure by a prime-to-`p`
monodromy proof. -/
noncomputable abbrev chosenPrimeToPClosure
    (p : ℕ) (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E]
    (hmono : IsPrimeToPMonodromy.{u, v, w} p K E) : Type w :=
  (chosenPrimeToPMonodromyCertificate p K E hmono).Closure

/-- The chosen normal closure is Galois and its group has order
prime to `p`. -/
theorem PrimeToPMonodromyCertificate.galoisGroupOrder_coprime
    (p : ℕ) (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E]
    (C : PrimeToPMonodromyCertificate.{u, v, w} p K E) :
    (Fintype.card Gal(C.Closure/K)).Coprime p := by
  letI : Field C.Closure := C.field
  letI : Algebra K C.Closure := C.algebra
  letI : FiniteDimensional K C.Closure := C.finiteClosure
  letI : IsGalois K C.Closure := C.isGaloisClosure
  classical
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  exact C.coprimeDegree

/-- The group-order hypothesis used by the fibre-factor theorem follows
directly from prime-to-`p` monodromy. -/
theorem chosenPrimeToPMonodromy_galoisGroupOrder_coprime
    (p : ℕ) (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E]
    (hmono : IsPrimeToPMonodromy.{u, v, w} p K E) :
    let C := chosenPrimeToPMonodromyCertificate p K E hmono
    (Fintype.card Gal(C.Closure/K)).Coprime p := by
  exact PrimeToPMonodromyCertificate.galoisGroupOrder_coprime p K E
    (chosenPrimeToPMonodromyCertificate p K E hmono)

/-- Every field factor of the reduced fibre of the certified normal
closure has prime-to-`p` monodromy, assuming the integral closure is
finite over the chosen normal affine base. -/
theorem PrimeToPMonodromyCertificate.fibreFactor_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E]
    (C : PrimeToPMonodromyCertificate.{u, v, w} p K E)
    (R : Type z) (F : Type x)
    [CommRing R] [IsDomain R] [Field F]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R C.Closure] [IsScalarTower R K C.Closure]
    [Algebra R F] [IsIntegrallyClosed R]
    [CharP R p] [CharP F p]
    [Module.Finite R (integralClosure R C.Closure)]
    (m : @MaximalSpectrum
      (GaloisIntegralClosureReducedFibre R C.Closure F)
      CommRing.toCommSemiring) :
    letI : Field
      (GaloisIntegralClosureReducedFibre R C.Closure F ⧸ m.asIdeal) := by
        exact Ideal.Quotient.field m.asIdeal
    IsPrimeToPMonodromy.{x, max w x, max w x} p F
      (GaloisIntegralClosureReducedFibre R C.Closure F ⧸ m.asIdeal) := by
  letI : IsGalois K C.Closure := C.isGaloisClosure
  exact galoisIntegralClosure_fibreFactor_primeToPMonodromy
    p hp R K C.Closure F (C.galoisGroupOrder_coprime p K E) m

/-- For a Noetherian normal affine base, finiteness of the integral
closure follows from finite separability of the certified Galois
extension, so each reduced fibre factor has prime-to-`p` monodromy. -/
theorem PrimeToPMonodromyCertificate.fibreFactor_primeToPMonodromy_of_noetherian
    (p : ℕ) (hp : p.Prime)
    (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E]
    (C : PrimeToPMonodromyCertificate.{u, v, w} p K E)
    (R : Type z) (F : Type x)
    [CommRing R] [IsDomain R] [Field F]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R C.Closure] [IsScalarTower R K C.Closure]
    [Algebra R F] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CharP R p] [CharP F p]
    (m : @MaximalSpectrum
      (GaloisIntegralClosureReducedFibre R C.Closure F)
      CommRing.toCommSemiring) :
    letI : Field
      (GaloisIntegralClosureReducedFibre R C.Closure F ⧸ m.asIdeal) := by
        exact Ideal.Quotient.field m.asIdeal
    IsPrimeToPMonodromy.{x, max w x, max w x} p F
      (GaloisIntegralClosureReducedFibre R C.Closure F ⧸ m.asIdeal) := by
  letI : IsGalois K C.Closure := C.isGaloisClosure
  letI : Algebra.IsSeparable K C.Closure := inferInstance
  letI : Module.Finite R (integralClosure R C.Closure) :=
    Stacks.IsIntegralClosure.moduleFinite_of_finiteSeparableExtension
      (A := R) (K := K) (L := C.Closure)
      (C := integralClosure R C.Closure)
  exact C.fibreFactor_primeToPMonodromy p hp K E R F m

/-- Starting from prime-to-`p` monodromy itself, every field factor of
the reduced fibre of its chosen Galois closure has prime-to-`p`
monodromy over the centre field. -/
theorem isPrimeToPMonodromy_chosenClosure_fibreFactor
    (p : ℕ) (hp : p.Prime)
    (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra K E]
    (hmono : IsPrimeToPMonodromy.{u, v, w} p K E)
    (R : Type z) (F : Type x)
    [CommRing R] [IsDomain R] [Field F]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R (chosenPrimeToPClosure p K E hmono)]
    [IsScalarTower R K (chosenPrimeToPClosure p K E hmono)]
    [Algebra R F] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CharP R p] [CharP F p]
    (m : @MaximalSpectrum
      (GaloisIntegralClosureReducedFibre R
        (chosenPrimeToPClosure p K E hmono) F)
      CommRing.toCommSemiring) :
    letI : Field
      (GaloisIntegralClosureReducedFibre R
        (chosenPrimeToPClosure p K E hmono) F ⧸ m.asIdeal) := by
        exact Ideal.Quotient.field m.asIdeal
    IsPrimeToPMonodromy.{x, max w x, max w x} p F
      (GaloisIntegralClosureReducedFibre R
        (chosenPrimeToPClosure p K E hmono) F ⧸ m.asIdeal) := by
  exact PrimeToPMonodromyCertificate.fibreFactor_primeToPMonodromy_of_noetherian
    p hp K E (chosenPrimeToPMonodromyCertificate p K E hmono) R F m

#print axioms chosenPrimeToPMonodromyCertificate
#print axioms chosenPrimeToPClosure
#print axioms PrimeToPMonodromyCertificate.galoisGroupOrder_coprime
#print axioms chosenPrimeToPMonodromy_galoisGroupOrder_coprime
#print axioms PrimeToPMonodromyCertificate.fibreFactor_primeToPMonodromy
#print axioms PrimeToPMonodromyCertificate.fibreFactor_primeToPMonodromy_of_noetherian
#print axioms isPrimeToPMonodromy_chosenClosure_fibreFactor

end Pcf
