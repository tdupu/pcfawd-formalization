/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GeometricCentreMonodromy
public import Pcf.Bounding.GaloisIntegralClosureInvariant
public import Pcf.Bounding.GlobalFiniteExtensionNormalization

/-!
# Monodromy at every centre of an intermediate normalization

For an actual finite Galois field extension, its integral closure has the
canonical Galois action and the original normal ring as invariant ring.
Finite-type normalization supplies finiteness of the integral closure. Thus
the affine all-centre monodromy theorem applies to any intermediate ring
embedded in that normalization.
-/

@[expose] public section

namespace Pcf

universe u v w x y

set_option linter.style.haveILetI false

/-- Every prime centre in an intermediate coordinate ring inside the
integral closure of a prime-to-`p` Galois function-field extension has
prime-to-`p` monodromy over its image centre. -/
theorem galoisNormalization_intermediate_centre_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [IsIntegrallyClosed R]
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type x) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CharP R p]
    (hdegree : (Module.finrank K L).Coprime p)
    (S : Type y) [CommRing S] [Algebra R S]
    (ι : S →ₐ[R] integralClosure R L)
    (hι : Function.Injective ι)
    (Q : Ideal S) [Q.IsPrime] :
    letI : Algebra (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := centreFieldAlgebra Q
    IsPrimeToPMonodromy.{v, y, max v x} p
      (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := by
  let B := integralClosure R L
  letI : Module.Finite R B :=
    finite_integralClosure_of_finiteType_finiteExtension k R K L
  letI : IsFractionRing B L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction R K L B
  have hact := integralClosure_galois_action_invariant R K L
  letI : SMulCommClass Gal(L/K) R B := hact.1
  letI : Algebra.IsInvariant R B Gal(L/K) := hact.2
  have horder : (Fintype.card Gal(L/K)).Coprime p := by
    rwa [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  exact intermediate_centre_primeToPMonodromy
    (R := R) (S := S) (B := B) (G := Gal(L/K))
    p hp horder ι hι Q

#print axioms galoisNormalization_intermediate_centre_primeToPMonodromy

end Pcf
