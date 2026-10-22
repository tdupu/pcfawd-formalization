/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeClosedImmersion

/-!
# Comparison of the relative Rees Proj chart maps

The chart map defined by the global `Proj.map` must agree with the closed
immersion obtained from the surjective tensor-product coordinate map.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] reesProjChartAlgebra

private theorem transportPullbackIso_inv_fst
    {X Y Z T : Scheme} (f : X ⟶ Z) {g h : Y ⟶ Z} (e : g = h)
    (i : Limits.pullback f h ≅ T) (q : T ⟶ X)
    (hi : i.inv ≫ Limits.pullback.fst f h = q) :
    (Eq.mpr (congrArg (fun k => Limits.pullback f k ≅ T) e) i).inv ≫
      Limits.pullback.fst f g = q := by
  cases e
  exact hi

private theorem transportPullbackIso_inv_snd
    {X Y Z T : Scheme} (f : X ⟶ Z) {g h : Y ⟶ Z} (e : g = h)
    (i : Limits.pullback f h ≅ T) (q : T ⟶ Y)
    (hi : i.inv ≫ Limits.pullback.snd f h = q) :
    (Eq.mpr (congrArg (fun k => Limits.pullback f k ≅ T) e) i).inv ≫
      Limits.pullback.snd f g = q := by
  cases e
  exact hi

private theorem chartPullbackIso_inv_fst (I : Ideal R) (a : I) :
    (reesProjChartPullbackIso (S := S) I a).inv ≫
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S (S ⊗[R] reesProjChart I a))) := by
  exact transportPullbackIso_inv_fst
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (reesProjChartOpen_toSpec_alg I a)
    (pullbackSpecIso R S (reesProjChart I a))
    (Spec.map (CommRingCat.ofHom
      (algebraMap S (S ⊗[R] reesProjChart I a))))
    (pullbackSpecIso_inv_fst' R S (reesProjChart I a))

private theorem chartPullbackIso_inv_snd (I : Ideal R) (a : I) :
    (reesProjChartPullbackIso (S := S) I a).inv ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          reesProjChart I a →ₐ[R] S ⊗[R] reesProjChart I a).toRingHom) := by
  exact transportPullbackIso_inv_snd
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (reesProjChartOpen_toSpec_alg I a)
    (pullbackSpecIso R S (reesProjChart I a))
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        reesProjChart I a →ₐ[R] S ⊗[R] reesProjChart I a).toRingHom))
    (pullbackSpecIso_inv_snd R S (reesProjChart I a))

/-- The fibre-product lift of the Proj chart map is exactly the closed
immersion produced by the surjective tensor-product coordinate map. -/
theorem reesProjChartRelativeBaseChange_eq_closedImmersion
    (I : Ideal R) (a : I) :
    reesProjChartRelativeBaseChange (S := S) I a =
      reesProjChartRelativeClosedImmersion (S := S) I a := by
  apply Limits.pullback.hom_ext
  · rw [reesProjChartRelativeBaseChange_fst]
    unfold reesProjChartRelativeClosedImmersion
    rw [Category.assoc, chartPullbackIso_inv_fst]
    rw [reesProjChartOpen_toSpec_alg]
    simp only [reesProjChartBaseChangeSpec, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
    congr 1
    apply RingHom.ext
    intro s
    exact ((reesProjChartBaseChange (S := S) I a).commutes s).symm
  · rw [reesProjChartRelativeBaseChange_snd]
    unfold reesProjChartRelativeClosedImmersion
    rw [Category.assoc, chartPullbackIso_inv_snd]
    simp only [reesProjChartBaseChangeSpec, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
    congr 1
    apply RingHom.ext
    intro z
    exact (reesProjChartBaseChange_one_tmul (S := S) I a z).symm

instance reesProjChartRelativeBaseChange_isClosedImmersion
    (I : Ideal R) (a : I) :
    IsClosedImmersion (reesProjChartRelativeBaseChange (S := S) I a) := by
  rw [reesProjChartRelativeBaseChange_eq_closedImmersion]
  infer_instance

#print axioms chartPullbackIso_inv_fst
#print axioms chartPullbackIso_inv_snd
#print axioms reesProjChartRelativeBaseChange_eq_closedImmersion
#print axioms reesProjChartRelativeBaseChange_isClosedImmersion

end Pcf.Bounding.AllCodimBlowup
