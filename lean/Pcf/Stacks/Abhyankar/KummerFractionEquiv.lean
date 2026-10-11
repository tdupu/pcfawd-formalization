/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.KummerFraction
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The fraction-field base-change equivalence for Stacks Tag 09EV

For the Eisenstein root algebra `B = A[X]/(X^n-π)`, this file constructs the canonical
`FractionRing A`-algebra equivalence

`FractionRing B ≃ AdjoinRoot (X^n-π : (FractionRing A)[X])`.

The construction first maps `B` to the displayed root field, proves injectivity by contracting
the kernel along the integral extension `A ⊆ B`, and extends this map to `FractionRing B`.
The extension is bijective because both sides have degree `n` over `FractionRing A`.

This supplies the fraction-field identification needed in clauses (1)--(4) of `09EV`.  It
does not classify intermediate fields and therefore is not labelled as the full tag.
-/

open Polynomial IsLocalRing

universe u

namespace Pcf.Stacks

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The canonical map from the integral root algebra to the root algebra over the fraction
field, obtained by mapping coefficients along `A → FractionRing A`. -/
noncomputable def dvrRootAlgebraToFractionRoot (π : A) (n : ℕ) :
    AdjoinRoot (dvrRootPoly π n) →+*
      AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n) :=
  AdjoinRoot.map (algebraMap A (FractionRing A)) _ _ <| by
    rw [dvrRootPoly_map_fractionRing]

/-- The canonical map to the fraction-field root algebra is injective. -/
theorem dvrRootAlgebraToFractionRoot_injective (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    Function.Injective (dvrRootAlgebraToFractionRoot π n) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    (dvrRootFractionAlgebra_isField π hn hπ).toField
  letI : Algebra.IsIntegral A (AdjoinRoot (dvrRootPoly π n)) :=
    AdjoinRoot.isIntegral_of_monic (dvrRootPoly_monic π hn)
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  have hunder_ne : (RingHom.ker (dvrRootAlgebraToFractionRoot π n)).under A ≠ ⊥ :=
    Ideal.IsIntegral.under_ne_bot A hker
  apply hunder_ne
  apply le_antisymm
  · intro a ha
    change dvrRootAlgebraToFractionRoot π n
      (AdjoinRoot.of (dvrRootPoly π n) a) = 0 at ha
    rw [dvrRootAlgebraToFractionRoot, AdjoinRoot.map_of] at ha
    have haK : (algebraMap A (FractionRing A)) a = 0 := by
      apply RingHom.injective
        (AdjoinRoot.of (dvrRootPoly (algebraMap A (FractionRing A) π) n))
      simpa only [map_zero] using ha
    apply IsFractionRing.injective A (FractionRing A)
    simpa only [map_zero] using haK
  · exact bot_le

/-- The lift of the canonical root-algebra map to the fraction ring of the integral root
algebra. -/
noncomputable def dvrRootFractionLift (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    FractionRing (AdjoinRoot (dvrRootPoly π n)) →+*
      AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    (dvrRootFractionAlgebra_isField π hn hπ).toField
  exact IsFractionRing.lift (dvrRootAlgebraToFractionRoot_injective π hn hπ)

/-- The fraction-ring lift restricts to the original canonical map on the integral root
algebra. -/
theorem dvrRootFractionLift_algebraMap (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) (x : AdjoinRoot (dvrRootPoly π n)) :
    dvrRootFractionLift π hn hπ (algebraMap (AdjoinRoot (dvrRootPoly π n))
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) x) =
      dvrRootAlgebraToFractionRoot π n x := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    (dvrRootFractionAlgebra_isField π hn hπ).toField
  exact IsFractionRing.lift_algebraMap
    (dvrRootAlgebraToFractionRoot_injective π hn hπ) x

/-- The `FractionRing A`-algebra structure on the fraction ring of the integral root
algebra, obtained by extending the scalar map from `A`. -/
@[instance_reducible]
noncomputable def dvrRootFractionRingAlgebra (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : FaithfulSMul A (AdjoinRoot (dvrRootPoly π n)) :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos (dvrRootPoly_monic π hn) <| by
      rw [← natDegree_pos_iff_degree_pos, dvrRootPoly, natDegree_X_pow_sub_C]
      exact hn
  letI : FaithfulSMul A (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    FaithfulSMul.trans A (AdjoinRoot (dvrRootPoly π n)) _
  exact FractionRing.liftAlgebra A _

/-- The fraction-ring lift is linear over `FractionRing A`. -/
noncomputable def dvrRootFractionLiftAlgHom (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
      dvrRootFractionRingAlgebra π hn hπ
    FractionRing (AdjoinRoot (dvrRootPoly π n)) →ₐ[FractionRing A]
      AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    (dvrRootFractionAlgebra_isField π hn hπ).toField
  letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    dvrRootFractionRingAlgebra π hn hπ
  letI : FaithfulSMul A (AdjoinRoot (dvrRootPoly π n)) :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos (dvrRootPoly_monic π hn) <| by
      rw [← natDegree_pos_iff_degree_pos, dvrRootPoly, natDegree_X_pow_sub_C]
      exact hn
  letI : FaithfulSMul A (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    FaithfulSMul.trans A (AdjoinRoot (dvrRootPoly π n)) _
  letI : IsScalarTower A (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    FractionRing.isScalarTower_liftAlgebra A _
  refine { dvrRootFractionLift π hn hπ with commutes' := ?_ }
  intro x
  have heq : (dvrRootFractionLift π hn hπ).comp
      (algebraMap (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n)))) =
      algebraMap (FractionRing A)
        (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    rw [RingHom.comp_apply]
    calc
      dvrRootFractionLift π hn hπ
          (algebraMap (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n)))
            (algebraMap A (FractionRing A) a)) =
          dvrRootFractionLift π hn hπ
            (algebraMap A (FractionRing (AdjoinRoot (dvrRootPoly π n))) a) :=
        congrArg (dvrRootFractionLift π hn hπ)
          (IsScalarTower.algebraMap_apply A (FractionRing A)
            (FractionRing (AdjoinRoot (dvrRootPoly π n))) a).symm
      _ = dvrRootFractionLift π hn hπ
          (algebraMap (AdjoinRoot (dvrRootPoly π n))
            (FractionRing (AdjoinRoot (dvrRootPoly π n)))
            (algebraMap A (AdjoinRoot (dvrRootPoly π n)) a)) :=
        congrArg (dvrRootFractionLift π hn hπ)
          (IsScalarTower.algebraMap_apply A (AdjoinRoot (dvrRootPoly π n))
            (FractionRing (AdjoinRoot (dvrRootPoly π n))) a)
      _ = dvrRootAlgebraToFractionRoot π n
          (algebraMap A (AdjoinRoot (dvrRootPoly π n)) a) :=
        dvrRootFractionLift_algebraMap π hn hπ _
      _ = dvrRootAlgebraToFractionRoot π n (AdjoinRoot.of (dvrRootPoly π n) a) := by
        rw [← AdjoinRoot.algebraMap_eq]
      _ = AdjoinRoot.of (dvrRootPoly (algebraMap A (FractionRing A) π) n)
          (algebraMap A (FractionRing A) a) := by
        rw [dvrRootAlgebraToFractionRoot, AdjoinRoot.map_of]
      _ = algebraMap (FractionRing A)
          (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n))
          (algebraMap A (FractionRing A) a) := by
        rw [AdjoinRoot.algebraMap_eq]
  exact DFunLike.congr_fun heq x

/-- The fraction field of the integral root algebra has degree `n` over `FractionRing A`. -/
theorem dvrRootFractionRing_finrank (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
      dvrRootFractionRingAlgebra π hn hπ
    Module.finrank (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) = n := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    dvrRootFractionRingAlgebra π hn hπ
  letI : FaithfulSMul A (AdjoinRoot (dvrRootPoly π n)) :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos (dvrRootPoly_monic π hn) <| by
      rw [← natDegree_pos_iff_degree_pos, dvrRootPoly, natDegree_X_pow_sub_C]
      exact hn
  letI : FaithfulSMul A (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    FaithfulSMul.trans A (AdjoinRoot (dvrRootPoly π n)) _
  letI : IsScalarTower A (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    FractionRing.isScalarTower_liftAlgebra A _
  calc
    Module.finrank (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) =
        Module.finrank A (AdjoinRoot (dvrRootPoly π n)) :=
      IsFractionRing.finrank_eq A (FractionRing A)
        (AdjoinRoot (dvrRootPoly π n)) (FractionRing (AdjoinRoot (dvrRootPoly π n)))
    _ = n := dvrRootAlgebra_finrank π hn

/-- The canonical fraction-ring lift is bijective. -/
theorem dvrRootFractionLiftAlgHom_bijective (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
      dvrRootFractionRingAlgebra π hn hπ
    Function.Bijective (dvrRootFractionLiftAlgHom π hn hπ) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    (dvrRootFractionAlgebra_isField π hn hπ).toField
  letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    dvrRootFractionRingAlgebra π hn hπ
  have hleft : Module.finrank (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) = n :=
    dvrRootFractionRing_finrank π hn hπ
  have hright : Module.finrank (FractionRing A)
      (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) = n :=
    dvrRootFractionAlgebra_finrank π hn
  have hleftpos : 0 < Module.finrank (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) := by
    rw [hleft]
    exact hn
  have hrightpos : 0 < Module.finrank (FractionRing A)
      (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) := by
    rw [hright]
    exact hn
  letI : FiniteDimensional (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    FiniteDimensional.of_finrank_pos hleftpos
  letI : FiniteDimensional (FractionRing A)
      (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    FiniteDimensional.of_finrank_pos hrightpos
  have hinj : Function.Injective (dvrRootFractionLiftAlgHom π hn hπ) :=
    RingHom.injective (dvrRootFractionLiftAlgHom π hn hπ).toRingHom
  refine ⟨hinj, ?_⟩
  have hlininj : Function.Injective (dvrRootFractionLiftAlgHom π hn hπ).toLinearMap := hinj
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (dvrRootFractionLiftAlgHom π hn hπ).toLinearMap)
    (hleft.trans hright.symm)).mp hlininj

/-- The canonical fraction-field/base-change equivalence for the root algebra in `09EV`. -/
noncomputable def dvrRootFractionEquiv (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
      dvrRootFractionRingAlgebra π hn hπ
    FractionRing (AdjoinRoot (dvrRootPoly π n)) ≃ₐ[FractionRing A]
      AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    (dvrRootFractionAlgebra_isField π hn hπ).toField
  letI : Algebra (FractionRing A) (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    dvrRootFractionRingAlgebra π hn hπ
  exact AlgEquiv.ofBijective (dvrRootFractionLiftAlgHom π hn hπ)
    (dvrRootFractionLiftAlgHom_bijective π hn hπ)

#print axioms dvrRootAlgebraToFractionRoot_injective
#print axioms dvrRootFractionLiftAlgHom
#print axioms dvrRootFractionRing_finrank
#print axioms dvrRootFractionLiftAlgHom_bijective
#print axioms dvrRootFractionEquiv

end Pcf.Stacks
