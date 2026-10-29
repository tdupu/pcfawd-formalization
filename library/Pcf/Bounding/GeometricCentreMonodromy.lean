/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GeometricCentreFieldEmbedding
public import Mathlib.Algebra.CharP.Quotient

/-!
# Prime-to-characteristic monodromy at every affine centre

This assembles the finite reduced-fibre construction, lying over,
stabilizer fixed fields, and the centre's field embedding. The
geometric input is an injective intermediate coordinate algebra
`S → B` inside a finite Galois normalization `B/R`.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.style.haveILetI false

universe u v w x

variable {R : Type u} {S : Type v} {B : Type w} {G : Type x}
  [CommRing R] [CommRing S] [CommRing B] [IsDomain B]
  [Algebra R S] [Algebra R B] [Module.Finite R B]
  [Group G] [Fintype G] [MulSemiringAction G B]
  [SMulCommClass G R B] [Algebra.IsInvariant R B G]

/-- The function-field extension at every prime centre of an
intermediate coordinate algebra has separable prime-to-`p` Galois
closure. -/
theorem intermediate_centre_primeToPMonodromy
    (p : ℕ) (hp : p.Prime) [CharP R p]
    (horder : (Fintype.card G).Coprime p)
    (ι : S →ₐ[R] B) (hι : Function.Injective ι)
    (Q : Ideal S) [Q.IsPrime] :
    letI : Algebra (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := centreFieldAlgebra Q
    IsPrimeToPMonodromy.{u, v, max u w} p
      (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := by
  let F := FractionRing (R ⧸ Q.under R)
  let E := FractionRing (S ⧸ Q)
  letI : Algebra F E := centreFieldAlgebra Q
  letI : CharP (R ⧸ Q.under R) p :=
    CharP.quotient' p (Q.under R) (by
      intro n hn
      by_contra hne
      have hnotdiv : ¬ p ∣ n := by
        intro hd
        exact hne ((CharP.cast_eq_zero_iff R p n).mpr hd)
      have hunit : IsUnit (n : R) :=
        (CharP.isUnit_natCast_iff hp).mpr hnotdiv
      exact (Ideal.notMem_of_isUnit (Q.under R) hunit) hn)
  letI : CharP F p := inferInstance
  obtain ⟨m, hker⟩ :=
    exists_tensorFibre_factor_over_intermediate_prime ι hι Q
  let L := ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal
  letI : Field L := Ideal.Quotient.field m.asIdeal
  have hL : IsPrimeToPMonodromy p F L :=
    tensorFibre_factor_primeToPMonodromy
      (R := R) (B := B) (F := F) (G := G) p hp horder m
  exact isPrimeToPMonodromy_of_algHom p F E L hL
    (centreFieldComponentAlgHom ι Q m hker)

#print axioms intermediate_centre_primeToPMonodromy

end Pcf
