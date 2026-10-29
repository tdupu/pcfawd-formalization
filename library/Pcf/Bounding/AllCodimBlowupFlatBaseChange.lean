/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupFlatCharts
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Rees Proj blow-ups commute with arbitrary flat affine base change

Bijective affine chart comparisons give isomorphisms on the standard target
cover. Their actual restrictions agree with the global relative Rees map.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
attribute [local instance] reesProjChartAlgebra

/-- The actual degree-zero Proj chart comparison is injective under flatness. -/
theorem reesProjChartBaseChange_injective (I : Ideal R) (a : I) :
    Function.Injective (reesProjChartBaseChange (S := S) I a) := by
  unfold reesProjChartBaseChange
  exact (reesProjChartAlgEquiv (I.map (algebraMap R S))
    (mappedCenterElement (algebraMap R S) I a)).symm.injective.comp
      ((affineBlowupChartBaseChange_injective I a).comp
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
          (reesProjChartAlgEquiv I a)).injective)

instance reesProjChartBaseChangeSpec_isIso (I : Ideal R) (a : I) :
    IsIso (reesProjChartBaseChangeSpec (B := S) I a) := by
  let φ := CommRingCat.ofHom (reesProjChartBaseChange (S := S) I a).toRingHom
  haveI : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).2
    ⟨reesProjChartBaseChange_injective I a, reesProjChartBaseChange_surjective I a⟩
  exact inferInstanceAs (IsIso (Spec.map φ))

instance reesProjChartRelativeBaseChange_isIso (I : Ideal R) (a : I) :
    IsIso (reesProjChartRelativeBaseChange (S := S) I a) := by
  rw [reesProjChartRelativeBaseChange_eq_closedImmersion]
  unfold reesProjChartRelativeClosedImmersion
  infer_instance

omit [Module.Flat R S] in
private theorem flatRelativeTargetCover_isPullback (I : Ideal R) (a : I) :
    IsPullback
      (reesProjChartRelativeBaseChange (S := S) I a ≫
        (Limits.pullbackLeftPullbackSndIso
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (reesProjToSpec I) (reesProjChartOpen I a)).inv)
      (reesProjChartOpen (I.map (algebraMap R S))
        (mappedCenterElement (algebraMap R S) I a))
      ((reesProjRelativeTargetCover (S := S) I).f a)
      (reesProjRelativeBaseChange (algebraMap R S) I) := by
  let e := Limits.pullbackLeftPullbackSndIso
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (reesProjToSpec I) (reesProjChartOpen I a)
  refine (reesProjRelativeBaseChange_chart_isPullback (S := S) I a).of_iso
    (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [e]
  · simp
  · rw [reesProjRelativeTargetCover_chart]
    simp [e]
  · simp

/-- The canonical relative Rees comparison is an isomorphism for an arbitrary
flat coefficient algebra, including trivial rings and zero ideals. -/
theorem reesProjRelativeBaseChange_isIso_of_flat (I : Ideal R) :
    IsIso (reesProjRelativeBaseChange (algebraMap R S) I) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover
    (P := .isomorphisms _) (reesProjRelativeTargetCover (S := S) I)).2
  intro a
  let h := (flatRelativeTargetCover_isPullback (S := S) I a).flip
  change IsIso (Limits.pullback.snd (reesProjRelativeBaseChange (algebraMap R S) I)
    ((reesProjRelativeTargetCover (S := S) I).f a))
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- Blow-up commutes with flat affine base change, as an actual Cartesian
square of the `Proj` schemes of the two Rees algebras.

**Divergence from Stacks 0805:** this proves its affine-base case. No domain,
nonzero-centre, nonempty-spectrum, or injectivity assumption is imposed. -/
@[stacks 0805 "affine bases; arbitrary flat coefficient algebra"]
theorem reesProjMap_isPullback_of_flat (I : Ideal R) :
    IsPullback (reesProjToSpec (I.map (algebraMap R S)))
      (reesProjMap (algebraMap R S) I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (reesProjToSpec I) := by
  letI := reesProjRelativeBaseChange_isIso_of_flat (S := S) I
  exact IsPullback.of_iso_pullback ⟨(reesProjMap_toSpec (algebraMap R S) I).symm⟩
    (asIso (reesProjRelativeBaseChange (algebraMap R S) I))
    (reesProjRelativeBaseChange_fst (algebraMap R S) I)
    (reesProjRelativeBaseChange_snd (algebraMap R S) I)

#print axioms reesProjRelativeBaseChange_isIso_of_flat
#print axioms reesProjMap_isPullback_of_flat
end
end Pcf.Bounding.AllCodimBlowup
