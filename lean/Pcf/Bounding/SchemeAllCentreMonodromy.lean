/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FiniteCoverAllCentreMonodromy
public import Pcf.Bounding.SchemePrimeToPSpecialization

/-!
# All-centre monodromy for a finite scheme morphism

On each affine target chart, the finite preimage is affine. Its actual
coordinate algebra and the generic stalk map supply the finite cover
required by the algebraic all-centre theorem. A point's prime ideal is
the reduced ideal of its closure, and its contraction is the prime
ideal of the image point.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- On a finite dominant morphism between integral schemes, every
prime centre on a finite affine preimage has prime-to-`p` monodromy
over its contracted centre. -/
theorem finiteNormalAffinePreimage_allCentre_primeToPMonodromy
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Algebra k Γ(Y, U)] [Algebra.FiniteType k Γ(Y, U)]
    [CharP Γ(Y, U) p]
    (hmono : IsPrimeToPMonodromyMap p f)
    (Q : Ideal Γ(X, finitePreimageAffine f U)) [Q.IsPrime] :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      (f.app U).hom.toAlgebra
    letI : Algebra
      (FractionRing (Γ(Y, U) ⧸ Q.under Γ(Y, U)))
      (FractionRing (Γ(X, finitePreimageAffine f U) ⧸ Q)) :=
      centreFieldAlgebra Q
    IsPrimeToPMonodromy.{u, u, u} p
      (FractionRing (Γ(Y, U) ⧸ Q.under Γ(Y, U)))
      (FractionRing (Γ(X, finitePreimageAffine f U) ⧸ Q)) := by
  let V := finitePreimageAffine f U
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  have hmem : f (genericPoint X) ∈ (U : Y.Opens) := by
    rw [hgp]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : Y.Opens)›)
  letI : Nonempty (V : X.Opens) := ⟨⟨genericPoint X, hmem⟩⟩
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let K := Y.presheaf.stalk (f (genericPoint X))
  let E := X.functionField
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField K := e.toMulEquiv.isField (Field.toIsField _)
  letI : Field K := hfield.toField
  letI : Algebra R K :=
    (Y.presheaf.germ U (f (genericPoint X)) hmem).hom.toAlgebra
  letI : IsFractionRing R K :=
    isFractionRing_targetGenericStalk_of_finiteDominant f U
  letI : IsFractionRing S E :=
    functionField_isFractionRing_of_isAffineOpen X V V.2
  letI : Algebra R E :=
    ((X.germToFunctionField V).hom.comp (f.app U).hom).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K E := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (f.germ_stalkMap_apply U (genericPoint X) hmem r).symm)
  exact finiteCover_allCentre_primeToPMonodromy
    p hp k R S K E hmono Q

/-- The prime centre of the reduced closure of a point lies above the
prime centre of the closure of its image. -/
theorem finitePreimage_pointClosure_under_eq_image
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) (x : X)
    (hx : x ∈ (finitePreimageAffine f U : X.Opens)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      (f.app U).hom.toAlgebra
    (((finitePreimageAffine f U).2.primeIdealOf ⟨x, hx⟩).asIdeal).under
      Γ(Y, U) =
      (U.2.primeIdealOf ⟨f x, hx⟩).asIdeal := by
  let V := finitePreimageAffine f U
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.app U).hom.toAlgebra
  have hAlg : algebraMap Γ(Y, U) Γ(X, V) =
      (f.appLE U V le_rfl).hom := by
    change (f.app U).hom = (f.appLE U V le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  change ((V.2.primeIdealOf ⟨x, hx⟩).asIdeal).comap
    (algebraMap Γ(Y, U) Γ(X, V)) =
    (U.2.primeIdealOf ⟨f x, hx⟩).asIdeal
  rw [hAlg]
  exact congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
      (V : X.Opens) V.2 le_rfl hx)

/-- The reduced integral closure of any point, in arbitrary
codimension, has prime-to-`p` function-field monodromy over the
closure of its image. The two prime ideals are the actual point-closure
ideal sheaves on the chosen affine chart. -/
theorem finiteNormalAffinePreimage_pointClosure_primeToPMonodromy
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (U : Y.affineOpens)
    [Algebra k Γ(Y, U)] [Algebra.FiniteType k Γ(Y, U)]
    [CharP Γ(Y, U) p]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) (hx : x ∈ (finitePreimageAffine f U : X.Opens)) :
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
  let V := finitePreimageAffine f U
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.app U).hom.toAlgebra
  let Q : Ideal Γ(X, V) := (pointClosureIdealSheaf x).ideal V
  let P : Ideal Γ(Y, U) := (pointClosureIdealSheaf (f x)).ideal U
  have hQ : Q = (V.2.primeIdealOf ⟨x, hx⟩).asIdeal :=
    pointClosureIdealSheaf_ideal x V hx
  letI : Q.IsPrime := by
    rw [hQ]
    infer_instance
  have hP : P = (U.2.primeIdealOf ⟨f x, hx⟩).asIdeal :=
    pointClosureIdealSheaf_ideal (f x) U hx
  have hcontract : Q.under Γ(Y, U) = P := by
    rw [hQ, hP]
    exact finitePreimage_pointClosure_under_eq_image f U x hx
  have hne : Nonempty (U : Y.Opens) := ⟨⟨f x, hx⟩⟩
  letI : Nonempty (U : Y.Opens) := hne
  exact ⟨hcontract,
    finiteNormalAffinePreimage_allCentre_primeToPMonodromy
      p hp k f U hmono Q⟩

#print axioms finiteNormalAffinePreimage_allCentre_primeToPMonodromy
#print axioms finitePreimage_pointClosure_under_eq_image
#print axioms finiteNormalAffinePreimage_pointClosure_primeToPMonodromy

end Pcf
