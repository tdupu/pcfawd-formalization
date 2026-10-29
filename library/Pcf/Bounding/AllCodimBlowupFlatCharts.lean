/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeGluing
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat base change of actual affine Rees charts

Flat tensoring preserves the inclusion of the actual chart `R[I/a]` in `R_a`.
Localization commutes with base change, so the already surjective Rees chart
comparison is injective as well. No domain or nonzero assumption is needed.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
noncomputable section
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The ambient localization base-change equivalence agrees with the actual
localization map on the original factor. -/
theorem awayTensorEquiv_one_tmul (a : R) (x : Localization.Away a) :
    IsLocalization.Away.tensorEquiv S a (Localization.Away a) ((1 : S) ⊗ₜ[R] x) =
      Localization.awayMap (algebraMap R S) a x := by
  let e := IsLocalization.Away.tensorEquiv S a (Localization.Away a)
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Localization.Away a →ₐ[R]
        S ⊗[R] Localization.Away a).toRingHom =
      Localization.awayMap (algebraMap R S) a := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    change e ((1 : S) ⊗ₜ[R] algebraMap R (Localization.Away a) r) =
      Localization.awayMap (algebraMap R S) a (algebraMap R (Localization.Away a) r)
    rw [show (1 : S) ⊗ₜ[R] algebraMap R (Localization.Away a) r =
      algebraMap S (S ⊗[R] Localization.Away a) (algebraMap R S r) by
        rw [← Algebra.TensorProduct.algebraMap_apply']
        exact (IsScalarTower.algebraMap_apply R S (S ⊗[R] Localization.Away a) r).symm]
    rw [e.commutes]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  exact DFunLike.congr_fun he x

/-- The actual affine-chart comparison, followed by its ambient inclusion,
agrees with tensoring the original inclusion and the localization equivalence. -/
theorem affineBlowupChartBaseChange_val (I : Ideal R) (a : I)
    (z : S ⊗[R] affineBlowupChart I a) :
    (affineBlowupChartBaseChange (S := S) I a z).1 =
      IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1)
        ((Subalgebra.val (affineBlowupChart I a)).toLinearMap.lTensor S z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul s x =>
      simp only [affineBlowupChartBaseChange, Algebra.TensorProduct.lift_tmul,
        LinearMap.lTensor_tmul]
      change algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        Localization.awayMap (algebraMap R S) a.1 x.1 =
        IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1) (s ⊗ₜ[R] x.1)
      rw [show s ⊗ₜ[R] x.1 =
        algebraMap S (S ⊗[R] Localization.Away a.1) s * ((1 : S) ⊗ₜ[R] x.1) by
          simp [Algebra.TensorProduct.algebraMap_apply]]
      rw [map_mul, AlgEquiv.commutes, awayTensorEquiv_one_tmul]

/-- Flatness makes the actual affine Rees chart base-change map injective,
including when the chosen chart element is zero or the chart ring is trivial. -/
theorem affineBlowupChartBaseChange_injective [Module.Flat R S]
    (I : Ideal R) (a : I) :
    Function.Injective (affineBlowupChartBaseChange (S := S) I a) := by
  intro x y hxy
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (M := S) (Subalgebra.val (affineBlowupChart I a)).toLinearMap Subtype.val_injective
  apply (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1)).injective
  rw [← affineBlowupChartBaseChange_val, ← affineBlowupChartBaseChange_val, hxy]

/-- Actual affine Rees charts commute with arbitrary flat coefficient change. -/
theorem affineBlowupChartBaseChange_bijective [Module.Flat R S]
    (I : Ideal R) (a : I) :
    Function.Bijective (affineBlowupChartBaseChange (S := S) I a) :=
  ⟨affineBlowupChartBaseChange_injective I a,
    affineBlowupChartBaseChange_surjective I a⟩

#print axioms affineBlowupChartBaseChange_injective
#print axioms affineBlowupChartBaseChange_bijective
end
end Pcf.Bounding.AllCodimBlowup
