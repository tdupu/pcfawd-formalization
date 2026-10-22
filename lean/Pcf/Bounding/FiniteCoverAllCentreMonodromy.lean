/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GaloisNormalizationAllCentre

/-!
# Prime-to-characteristic monodromy at all centres of a finite cover

The generic prime-to-characteristic monodromy certificate contains a
finite Galois closure. A finite intermediate cover embeds into the
integral closure of the base in that closure. Consequently, the
function-field extension at every prime centre is again prime to the
characteristic.
-/

@[expose] public section

namespace Pcf

universe u v

set_option linter.style.haveILetI false

/-- Algebraic form of the arbitrary-codimension monodromy
specialization lemma. The centre is any prime ideal of the finite
cover, with no codimension restriction. -/
theorem finiteCover_allCentre_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type v) [Field k]
    (R S K E : Type u)
    [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    [Field K] [Field E]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E]
    [CharP R p]
    (hmono : IsPrimeToPMonodromy.{u, u, u} p K E)
    (Q : Ideal S) [Q.IsPrime] :
    letI : Algebra (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := centreFieldAlgebra Q
    IsPrimeToPMonodromy.{u, u, u} p
      (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := by
  obtain ⟨C⟩ := hmono
  letI : Field C.Closure := C.field
  letI : Algebra K C.Closure := C.algebra
  letI : FiniteDimensional K C.Closure := C.finiteClosure
  letI : IsGalois K C.Closure := C.isGaloisClosure
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  letI : Algebra R C.Closure :=
    ((algebraMap K C.Closure).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K C.Closure := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S C.Closure :=
    (C.embedding.toRingHom.comp (algebraMap S E)).toAlgebra
  letI : IsScalarTower R S C.Closure := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap K C.Closure (algebraMap R K r) =
      C.embedding (algebraMap S E (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S E]
    calc
      algebraMap K C.Closure (algebraMap R K r) =
          C.embedding (algebraMap K E (algebraMap R K r)) :=
        (C.embedding.commutes _).symm
      _ = C.embedding (algebraMap R E r) := by
        rw [IsScalarTower.algebraMap_apply R K E])
  let B := integralClosure R C.Closure
  let ι : S →ₐ[R] B := IsIntegralClosure.lift R B C.Closure
  have hι : Function.Injective ι := by
    intro s t h
    have h' := congrArg (algebraMap B C.Closure) h
    change algebraMap B C.Closure (ι s) = algebraMap B C.Closure (ι t) at h'
    rw [IsIntegralClosure.algebraMap_lift,
      IsIntegralClosure.algebraMap_lift] at h'
    exact (IsFractionRing.injective S E) (C.embedding.injective h')
  exact galoisNormalization_intermediate_centre_primeToPMonodromy
    p hp k R K C.Closure C.coprimeDegree S ι hι Q

#print axioms finiteCover_allCentre_primeToPMonodromy

end Pcf
