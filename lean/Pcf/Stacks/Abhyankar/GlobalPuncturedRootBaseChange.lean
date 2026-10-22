/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.DivisorNormalizationTransport

/-!
# The literal punctured tensor in the divisor branch of Tag 0EYG

For a ring `A`, an `A`-algebra `B` in which `a : A` is invertible, and the standard
root cover

`C = A[z] / (z^e - a)`,

the generic algebra in Stacks Tag `0EYG` is literally

`B ⊗[A[1/a]] C[1/a]`.

This file keeps that tensor product visible.  It first identifies it canonically with
`B ⊗[A] C`.  It then specializes `B` to the punctured upper DVR and identifies the
result with `DVRRootPuncturedBaseChange`, the exact generic algebra consumed by the
formalized `0BRM` endpoint.  The distinguished-root formula is recorded explicitly; it
is the compatibility needed to compare the global standard-root map with the map produced
by the DVR normalization square.

No normalization, unramifiedness, or etaleness statement is assumed here.
-/

universe u

namespace Pcf.Stacks

set_option linter.style.haveILetI false

noncomputable section

/-- The algebra structure on `B` over `A[1/a]` induced by the fact that `a` is already a
unit in `B`. -/
@[instance_reducible]
noncomputable def awayAlgebraOfIsUnit
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (ha : IsUnit (algebraMap A B a)) :
    Algebra (Localization.Away a) B :=
  (IsLocalization.Away.liftAlgHom
    (S := Localization.Away a) (f := Algebra.ofId A B) a ha).toRingHom.toAlgebra

/-- The literal punctured tensor from Tag `0EYG`:
`B ⊗[A[1/a]] (A[z]/(z^e-a))[1/a]`.

The right localization is written using the image of `Submonoid.powers a`; this is
definitionally the target of `Localization.tensorRightAlgEquiv` and is canonically the
usual localization away from the image of `a`. -/
abbrev LiteralPuncturedRootBaseChange
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (exponent : ℕ) (ha : IsUnit (algebraMap A B a)) :=
  let Af := Localization.Away a
  let C := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)
  let Cf := Localization
    (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
  let _ : Algebra Af B := awayAlgebraOfIsUnit A B a ha
  B ⊗[Af] Cf

/-- The distinguished global root inside the literal punctured tensor. -/
noncomputable def literalPuncturedRoot
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (exponent : ℕ) (ha : IsUnit (algebraMap A B a)) :
    LiteralPuncturedRootBaseChange A B a exponent ha := by
  let Af := Localization.Away a
  let C := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)
  let Cf := Localization
    (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
  letI : Algebra Af B := awayAlgebraOfIsUnit A B a ha
  exact 1 ⊗ₜ[Af] algebraMap C Cf
    (AdjoinRoot.root (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))

/-- Once `a` is a unit in `B`, the literal punctured tensor is canonically the ordinary
base change `B ⊗[A] A[z]/(z^e-a)`.

The proof first writes the localized root algebra as
`A[1/a] ⊗[A] A[z]/(z^e-a)` and then cancels the intermediate base change. -/
noncomputable def literalPuncturedRootBaseChangeEquiv
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (exponent : ℕ) (ha : IsUnit (algebraMap A B a)) :
    LiteralPuncturedRootBaseChange A B a exponent ha ≃ₐ[B]
      B ⊗[A] AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent) := by
  let Af := Localization.Away a
  let C := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)
  let Cf := Localization
    (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
  letI : Algebra Af B := awayAlgebraOfIsUnit A B a ha
  letI : IsScalarTower A Af B := IsScalarTower.of_algebraMap_eq fun x ↦ by
    exact (IsLocalization.Away.liftAlgHom
      (S := Af) (f := Algebra.ofId A B) a ha).commutes x |>.symm
  let eC : Af ⊗[A] C ≃ₐ[Af] Cf :=
    Localization.tensorRightAlgEquiv (Submonoid.powers a) C
  exact
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eC.symm).trans
      (Algebra.TensorProduct.cancelBaseChange A Af B B C)

/-- The preceding equivalence sends the literal distinguished root to the ordinary
base-changed distinguished root. -/
@[simp]
theorem literalPuncturedRootBaseChangeEquiv_root
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (exponent : ℕ) (ha : IsUnit (algebraMap A B a)) :
    literalPuncturedRootBaseChangeEquiv A B a exponent ha
        (literalPuncturedRoot A B a exponent ha) =
      (1 : B) ⊗ₜ[A]
        AdjoinRoot.root (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent) := by
  let Af := Localization.Away a
  let C := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)
  let Cf := Localization
    (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
  letI : Algebra Af B := awayAlgebraOfIsUnit A B a ha
  letI : IsScalarTower A Af B := IsScalarTower.of_algebraMap_eq fun x ↦ by
    exact (IsLocalization.Away.liftAlgHom
      (S := Af) (f := Algebra.ofId A B) a ha).commutes x |>.symm
  let eC : Af ⊗[A] C ≃ₐ[Af] Cf :=
    Localization.tensorRightAlgEquiv (Submonoid.powers a) C
  change
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eC.symm).trans
      (Algebra.TensorProduct.cancelBaseChange A Af B B C))
        (1 ⊗ₜ[Af] algebraMap C Cf (AdjoinRoot.root
          (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))) = _
  have hroot : eC.symm (algebraMap C Cf (AdjoinRoot.root
      (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))) =
      (1 : Af) ⊗ₜ[A]
        AdjoinRoot.root (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent) := by
    apply eC.injective
    simp [eC]
  simp [hroot]

/-- Base change of the global standard root algebra first to `A_p` and then to an
`A_p`-algebra `S` agrees with direct base change to `S`, and the `A_p` factor is the
literal DVR standard-root algebra from Tag `09EV`. -/
noncomputable def standardRootBaseChangeToUpperEquiv
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime]
    [Algebra (Localization.AtPrime p) S]
    [IsScalarTower A (Localization.AtPrime p) S]
    (a : A) (exponent : ℕ) :
    S ⊗[A] AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent) ≃ₐ[S]
      S ⊗[Localization.AtPrime p]
        AdjoinRoot (dvrRootPoly
          (algebraMap A (Localization.AtPrime p) a) exponent) :=
  (Algebra.TensorProduct.cancelBaseChange
      A (Localization.AtPrime p) S S
      (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (standardRootTensorAtPrimeEquivDVRRoot A p a exponent))

/-- The upper base-change equivalence preserves the distinguished root. -/
@[simp]
theorem standardRootBaseChangeToUpperEquiv_root
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime]
    [Algebra (Localization.AtPrime p) S]
    [IsScalarTower A (Localization.AtPrime p) S]
    (a : A) (exponent : ℕ) :
    standardRootBaseChangeToUpperEquiv A S p a exponent
        ((1 : S) ⊗ₜ[A]
          AdjoinRoot.root (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)) =
      (1 : S) ⊗ₜ[Localization.AtPrime p]
        AdjoinRoot.root (dvrRootPoly
          (algebraMap A (Localization.AtPrime p) a) exponent) := by
  simp [standardRootBaseChangeToUpperEquiv,
    standardRootTensorAtPrimeEquivDVRRoot_root]

/-- The canonical algebra structure from the global standard root cover to its divisor
localization.  This is the reusable form of the algebra structure constructed internally
in `standardRoot_dvrRoot_isLocalizationAtDivisorPrime`. -/
@[instance_reducible]
noncomputable def standardRootDVRRootAlgebra
    (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (a : A) (exponent : ℕ) :
    Algebra (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))
      (AdjoinRoot (dvrRootPoly
        (algebraMap A (Localization.AtPrime p) a) exponent)) :=
  ((standardRootTensorAtPrimeEquivDVRRoot A p a exponent).toAlgHom.restrictScalars A).comp
    (Algebra.TensorProduct.includeRight
      (R := A) (A := Localization.AtPrime p)
      (B := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)))
  |>.toRingHom.toAlgebra

/-- On coefficients, the global-to-DVR standard-root map is the canonical composite
through `A_p`. -/
theorem standardRootDVRRootAlgebra_algebraMap
    (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (a : A) (exponent : ℕ) (x : A) :
    let _ : Algebra (AdjoinRoot
        (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))
        (AdjoinRoot (dvrRootPoly
          (algebraMap A (Localization.AtPrime p) a) exponent)) :=
      standardRootDVRRootAlgebra A p a exponent
    algebraMap (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))
        (AdjoinRoot (dvrRootPoly
          (algebraMap A (Localization.AtPrime p) a) exponent))
        (algebraMap A
          (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)) x) =
      algebraMap (Localization.AtPrime p)
        (AdjoinRoot (dvrRootPoly
          (algebraMap A (Localization.AtPrime p) a) exponent))
        (algebraMap A (Localization.AtPrime p) x) := by
  dsimp only
  exact (standardRootTensorAtPrimeEquivDVRRoot A p a exponent).commutes
    (algebraMap A (Localization.AtPrime p) x)

/-- On the distinguished generator, the global-to-DVR map is the local standard root. -/
theorem standardRootDVRRootAlgebra_root
    (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (a : A) (exponent : ℕ) :
    let _ : Algebra (AdjoinRoot
        (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))
        (AdjoinRoot (dvrRootPoly
          (algebraMap A (Localization.AtPrime p) a) exponent)) :=
      standardRootDVRRootAlgebra A p a exponent
    algebraMap (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))
        (AdjoinRoot (dvrRootPoly
          (algebraMap A (Localization.AtPrime p) a) exponent))
        (AdjoinRoot.root
          (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent)) =
      AdjoinRoot.root (dvrRootPoly
        (algebraMap A (Localization.AtPrime p) a) exponent) := by
  dsimp only
  exact standardRootTensorAtPrimeEquivDVRRoot_root A p a exponent

/-- In the upper punctured DVR, the divisor equation is a unit as soon as it is a unit
times a power of the chosen upper uniformizer. -/
theorem isUnit_map_to_away_of_eq_unit_mul_pow
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (a : A) (piS : S) (unit : Sˣ) (exponent : ℕ)
    (hfactor : algebraMap A S a = (unit : S) * piS ^ exponent) :
    IsUnit (algebraMap A (Localization.Away piS) a) := by
  rw [IsScalarTower.algebraMap_apply A S (Localization.Away piS),
    hfactor, map_mul, map_pow]
  exact ((Units.isUnit unit).map (algebraMap S (Localization.Away piS))).mul
    ((IsLocalization.Away.algebraMap_isUnit piS).pow exponent)

/-- The literal punctured tensor in Tag `0EYG`, localized along an upper DVR, is the
punctured `09EV` base-change square used by the `0BRM` endpoint. -/
noncomputable def literalPuncturedRootBaseChangeEquivDVRRoot
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime]
    [Algebra (Localization.AtPrime p) S]
    [IsScalarTower A (Localization.AtPrime p) S]
    (a : A) (piS : S) (unit : Sˣ) (exponent : ℕ)
    (hfactor : algebraMap A S a = (unit : S) * piS ^ exponent) :
    let B := Localization.Away piS
    let ha : IsUnit (algebraMap A B a) :=
      isUnit_map_to_away_of_eq_unit_mul_pow A S a piS unit exponent hfactor
    LiteralPuncturedRootBaseChange A B a exponent ha ≃ₐ[B]
      DVRRootPuncturedBaseChange
        (Localization.AtPrime p) S
        (algebraMap A (Localization.AtPrime p) a) piS exponent := by
  dsimp only
  let B := Localization.Away piS
  let ha : IsUnit (algebraMap A B a) :=
    isUnit_map_to_away_of_eq_unit_mul_pow A S a piS unit exponent hfactor
  letI : Algebra (Localization.AtPrime p) B :=
    ((algebraMap S B).comp
      (algebraMap (Localization.AtPrime p) S)).toAlgebra
  letI : IsScalarTower (Localization.AtPrime p) S B :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    (literalPuncturedRootBaseChangeEquiv A B a exponent ha).trans
      ((Algebra.TensorProduct.cancelBaseChange A S B B
        (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a exponent))).symm.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
          (standardRootBaseChangeToUpperEquiv A S p a exponent)))

/-- The literal-to-DVR comparison carries the global root to the root in the local
`09EV` tensor factor. -/
@[simp]
theorem literalPuncturedRootBaseChangeEquivDVRRoot_root
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime]
    [Algebra (Localization.AtPrime p) S]
    [IsScalarTower A (Localization.AtPrime p) S]
    (a : A) (piS : S) (unit : Sˣ) (exponent : ℕ)
    (hfactor : algebraMap A S a = (unit : S) * piS ^ exponent) :
    let B := Localization.Away piS
    let ha : IsUnit (algebraMap A B a) :=
      isUnit_map_to_away_of_eq_unit_mul_pow A S a piS unit exponent hfactor
    literalPuncturedRootBaseChangeEquivDVRRoot
        A S p a piS unit exponent hfactor
        (literalPuncturedRoot A B a exponent ha) =
      (1 : B) ⊗ₜ[S]
        ((1 : S) ⊗ₜ[Localization.AtPrime p]
          AdjoinRoot.root (dvrRootPoly
            (algebraMap A (Localization.AtPrime p) a) exponent)) := by
  dsimp only
  let B := Localization.Away piS
  let ha : IsUnit (algebraMap A B a) :=
    isUnit_map_to_away_of_eq_unit_mul_pow A S a piS unit exponent hfactor
  letI : Algebra (Localization.AtPrime p) B :=
    ((algebraMap S B).comp
      (algebraMap (Localization.AtPrime p) S)).toAlgebra
  letI : IsScalarTower (Localization.AtPrime p) S B :=
    IsScalarTower.of_algebraMap_eq' rfl
  simp [literalPuncturedRootBaseChangeEquivDVRRoot,
    literalPuncturedRootBaseChangeEquiv_root,
    standardRootBaseChangeToUpperEquiv_root]

#print axioms literalPuncturedRootBaseChangeEquiv
#print axioms literalPuncturedRootBaseChangeEquiv_root
#print axioms standardRootBaseChangeToUpperEquiv
#print axioms standardRootBaseChangeToUpperEquiv_root
#print axioms standardRootDVRRootAlgebra
#print axioms standardRootDVRRootAlgebra_algebraMap
#print axioms standardRootDVRRootAlgebra_root
#print axioms isUnit_map_to_away_of_eq_unit_mul_pow
#print axioms literalPuncturedRootBaseChangeEquivDVRRoot
#print axioms literalPuncturedRootBaseChangeEquivDVRRoot_root

end

end Pcf.Stacks
