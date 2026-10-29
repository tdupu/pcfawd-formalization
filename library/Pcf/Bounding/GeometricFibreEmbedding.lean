/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GeometricFibreBridge
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# A centre's function field inside a reduced fibre component

For an intermediate algebra `S` of a finite Galois normalization `B/R`,
each field factor of the reduced tensor fibre `B ⊗[R] F` receives a map
from `S`. Its kernel is a prime ideal `Q`, and the induced map on
`S/Q` extends to a field embedding from `Frac(S/Q)` into that factor.

The missing geometric selection step is to show that a *prescribed*
generic point `Q` of a subvariety of `Y` is the kernel for some factor.
This requires lying over in the intermediate integral extension.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.style.haveILetI false

universe u v w x y

variable {R : Type u} {S : Type v} {B : Type w} {F : Type x}
  [CommRing R] [CommRing S] [CommRing B] [Field F]
  [Algebra R S] [Algebra R B] [Algebra R F]

/-- The map from an intermediate coordinate algebra to one field
component of the reduced tensor fibre. -/
def tensorFibreComponentMap
    (ι : S →ₐ[R] B)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    S →+* (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) :=
  (Ideal.Quotient.mk m.asIdeal).comp <|
    (Ideal.Quotient.mk (nilradical (B ⊗[R] F))).comp <|
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] F).toRingHom.comp
        ι.toRingHom

/-- A component map sends base scalars to their images in the
centre's function field. -/
@[simp] theorem tensorFibreComponentMap_algebraMap
    (ι : S →ₐ[R] B)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)))
    (r : R) :
    tensorFibreComponentMap (F := F) ι m (algebraMap R S r) =
      algebraMap F
        (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal)
          (algebraMap R F r) := by
  simp only [tensorFibreComponentMap, RingHom.comp_apply]
  rw [show ι.toRingHom (algebraMap R S r) = algebraMap R B r from ι.commutes r]
  change (Ideal.Quotient.mk m.asIdeal)
      ((Ideal.Quotient.mk (nilradical (B ⊗[R] F)))
        ((algebraMap R B r) ⊗ₜ[R] (1 : F))) = _
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rfl

/-- The component's contraction to the intermediate algebra is prime. -/
theorem tensorFibreComponentMap_ker_isPrime
    (ι : S →ₐ[R] B)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    (RingHom.ker (tensorFibreComponentMap (F := F) ι m)).IsPrime := by
  letI : Field
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  exact RingHom.ker_isPrime _

/-- Every field component of the fibre contracts to the chosen base
centre. The contraction follows from injectivity of the scalar map
from a field into a field factor. -/
theorem tensorFibreComponentMap_ker_under
    (ι : S →ₐ[R] B)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    (RingHom.ker (tensorFibreComponentMap (F := F) ι m)).under R =
      RingHom.ker (algebraMap R F) := by
  letI : Field
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  ext r
  simp only [Ideal.mem_under, RingHom.mem_ker,
    tensorFibreComponentMap_algebraMap]
  simp

/-- The function field of the contracted centre embeds in the selected
field component. This is the algebraic part of the lying-over step in
`lem:allcodim-monodromy`. -/
noncomputable def tensorFibreComponentFractionEmbedding
    (ι : S →ₐ[R] B)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    letI : Field
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) :=
      Ideal.Quotient.field m.asIdeal
    FractionRing
      (S ⧸ RingHom.ker (tensorFibreComponentMap (F := F) ι m)) →+*
        (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) := by
  letI : Field
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  let φ := tensorFibreComponentMap (F := F) ι m
  letI : (RingHom.ker φ).IsPrime := tensorFibreComponentMap_ker_isPrime (F := F) ι m
  exact IsFractionRing.lift (RingHom.kerLift_injective φ)

section CompatibleField

variable {K : Type y} [Field K] [Algebra R K] [Algebra F K]
  [IsScalarTower R F K]

/-- Evaluation of the tensor fibre in a field receiving the
normalization, provided its two base maps are compatible. -/
def tensorFibreEvaluation (β : B →ₐ[R] K) : B ⊗[R] F →ₐ[F] K :=
  (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId F K) β).comp
    (Algebra.TensorProduct.commRight R F B).symm.toAlgHom

@[simp] theorem tensorFibreEvaluation_tmul
    (β : B →ₐ[R] K) (b : B) (a : F) :
    tensorFibreEvaluation (F := F) β (b ⊗ₜ[R] a) = β b * algebraMap F K a := by
  simp [tensorFibreEvaluation, mul_comm]

/-- The kernel of evaluation is a maximal ideal of the finite tensor
fibre: it is prime, and finite integrality over `F` makes it maximal. -/
theorem tensorFibreEvaluation_ker_isMaximal
    [Module.Finite R B] (β : B →ₐ[R] K) :
    (RingHom.ker (tensorFibreEvaluation (F := F) β).toRingHom).IsMaximal := by
  let C := B ⊗[R] F
  let ψ := tensorFibreEvaluation (F := F) β
  let I := RingHom.ker ψ.toRingHom
  letI : Module.Finite F C := tensorFibre_finiteDimensional
  letI : Algebra.IsIntegral F C := Algebra.IsIntegral.of_finite F C
  letI : I.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  have hunder : I.under F = ⊥ := by
    ext a
    simp only [Ideal.mem_under, Ideal.mem_bot]
    change ψ (algebraMap F C a) = 0 ↔ a = 0
    rw [ψ.commutes]
    simp
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under I
    (by rw [hunder]; exact Ideal.bot_isMaximal)

end CompatibleField

#print axioms tensorFibreComponentMap_ker_isPrime
#print axioms tensorFibreComponentMap_ker_under
#print axioms tensorFibreComponentFractionEmbedding
#print axioms tensorFibreEvaluation_ker_isMaximal

end Pcf
