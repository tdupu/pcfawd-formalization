/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PointClosureFunctionField
public import Pcf.Bounding.PcfAllTheWayDownScheme

/-!
# All-centre specialization over a field of characteristic p

The algebraic all-centre theorem asks for characteristic `p` and finite-type
coordinate rings. An actual finite-type scheme over a field of characteristic
`p` supplies these chart hypotheses automatically.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- On an affine chart of an integral finite-type scheme over a field of
characteristic `p`, the coordinate ring has characteristic `p`. -/
theorem schemeAffineAlgebraOfField_charP
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {Y : Scheme.{u}} [IsIntegral Y]
    (s : Y ⟶ Spec (.of k))
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)] :
    CharP Γ(Y, U) p := by
  letI : Algebra k Γ(Y, U) := schemeAffineAlgebraOfField k s U
  exact CharP.of_ringHom_of_ne_zero (algebraMap k Γ(Y, U)) p hp.ne_zero

/-- Every original reduced point closure in a finite cover of a normal
finite-type scheme over a characteristic-`p` field has affine quotient-field
monodromy prime to `p`; the characteristic and finite-type chart premises
come from the actual structure morphism. -/
theorem finiteType_pointClosure_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (U : Y.affineOpens) (x : X)
    (hx : x ∈ (finitePreimageAffine f U : X.Opens)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      (f.app U).hom.toAlgebra
    let Q : Ideal Γ(X, finitePreimageAffine f U) :=
      (pointClosureIdealSheaf x).ideal (finitePreimageAffine f U)
    let P : Ideal Γ(Y, U) := (pointClosureIdealSheaf (f x)).ideal U
    letI : Q.IsPrime :=
      pointClosureIdealSheaf_ideal_isPrime x (finitePreimageAffine f U) hx
    Q.under Γ(Y, U) = P ∧
      (letI : Algebra (FractionRing (Γ(Y, U) ⧸ Q.under Γ(Y, U)))
          (FractionRing (Γ(X, finitePreimageAffine f U) ⧸ Q)) :=
          centreFieldAlgebra Q;
        IsPrimeToPMonodromy.{u, u, u} p
          (FractionRing (Γ(Y, U) ⧸ Q.under Γ(Y, U)))
          (FractionRing (Γ(X, finitePreimageAffine f U) ⧸ Q))) := by
  have hne : Nonempty (U : Y.Opens) := ⟨⟨f x, hx⟩⟩
  letI : Nonempty (U : Y.Opens) := hne
  letI : Algebra k Γ(Y, U) := schemeAffineAlgebraOfField k s U
  letI : Algebra.FiniteType k Γ(Y, U) :=
    schemeAffineAlgebraOfField_finiteType k s U
  letI : CharP Γ(Y, U) p := schemeAffineAlgebraOfField_charP p hp k s U
  exact finiteNormalAffinePreimage_pointClosure_primeToPMonodromy
    p hp k f U hmono x hx

#print axioms schemeAffineAlgebraOfField_charP
#print axioms finiteType_pointClosure_primeToPMonodromy

end Pcf
