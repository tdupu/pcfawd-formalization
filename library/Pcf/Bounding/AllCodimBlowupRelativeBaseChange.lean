/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupChartCompatibility
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Relative base change on standard Rees Proj charts

The degree-zero Proj chart of the extended center is a closed subscheme of
the base change of the original chart. The map is defined by transporting
the explicit affine Rees-chart tensor map across the proved Proj-chart
equivalences, and agrees with the chart map of `Proj.map`.
-/

@[expose] public section

open scoped TensorProduct
open Polynomial

namespace Pcf.Bounding.AllCodimBlowup

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The base-ring algebra structure on a degree-zero Rees Proj chart,
transported from its explicit affine blow-up chart. -/
@[instance_reducible]
def reesProjChartAlgebra (I : Ideal R) (a : I) :
    Algebra R (reesProjChart I a) :=
  ((reesProjChartEquiv I a).symm.toRingHom.comp
    (algebraMap R (affineBlowupChart I a))).toAlgebra

attribute [local instance] reesProjChartAlgebra

/-- The degree-zero Proj chart equivalence respects the structural map from
the affine base. -/
def reesProjChartAlgEquiv (I : Ideal R) (a : I) :
    reesProjChart I a ≃ₐ[R] affineBlowupChart I a :=
  AlgEquiv.ofRingEquiv (f := reesProjChartEquiv I a) (by
    intro r
    exact (reesProjChartEquiv I a).apply_symm_apply
      (algebraMap R (affineBlowupChart I a) r))

/-- The canonical tensor-product map on actual Proj chart rings. Its
coefficientwise description follows from `reesProjChartMap_equiv_comm`. -/
def reesProjChartBaseChange (I : Ideal R) (a : I) :
    (S ⊗[R] reesProjChart I a) →ₐ[S]
      (reesProjChart (I.map (algebraMap R S))
        (mappedCenterElement (algebraMap R S) I a)) :=
  (reesProjChartAlgEquiv (I.map (algebraMap R S))
      (mappedCenterElement (algebraMap R S) I a)).symm.toAlgHom.comp
    ((affineBlowupChartBaseChange (S := S) I a).comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
        (reesProjChartAlgEquiv I a)).toAlgHom)

/-- The relative map on each standard Proj chart is surjective on rings. -/
theorem reesProjChartBaseChange_surjective (I : Ideal R) (a : I) :
    Function.Surjective (reesProjChartBaseChange (S := S) I a) := by
  intro z
  obtain ⟨x, hx⟩ := affineBlowupChartBaseChange_surjective (S := S) I a
    ((reesProjChartAlgEquiv (I.map (algebraMap R S))
      (mappedCenterElement (algebraMap R S) I a)) z)
  refine ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (reesProjChartAlgEquiv I a)).symm x, ?_⟩
  have hmap : Algebra.TensorProduct.map (AlgHom.id S S)
      (reesProjChartAlgEquiv I a).toAlgHom =
      (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
        (reesProjChartAlgEquiv I a)).toAlgHom := rfl
  have hcancel :
      (Algebra.TensorProduct.map (AlgHom.id S S)
        (reesProjChartAlgEquiv I a).toAlgHom)
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
          (reesProjChartAlgEquiv I a)).symm x) = x := by
    rw [hmap]
    exact AlgEquiv.apply_symm_apply _ x
  exact (reesProjChartAlgEquiv (I.map (algebraMap R S))
    (mappedCenterElement (algebraMap R S) I a)).injective (by
      calc
        (reesProjChartAlgEquiv (I.map (algebraMap R S))
            (mappedCenterElement (algebraMap R S) I a))
            (reesProjChartBaseChange (S := S) I a
              ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
                (reesProjChartAlgEquiv I a)).symm x)) =
          (affineBlowupChartBaseChange (S := S) I a)
            ((Algebra.TensorProduct.map (AlgHom.id S S)
              (reesProjChartAlgEquiv I a).toAlgHom)
              ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
                (reesProjChartAlgEquiv I a)).symm x)) := by
                simp only [reesProjChartBaseChange, AlgHom.comp_apply, hmap]
                exact (reesProjChartAlgEquiv (I.map (algebraMap R S))
                  (mappedCenterElement (algebraMap R S) I a)).apply_symm_apply _
        _ = (affineBlowupChartBaseChange (S := S) I a) x := by rw [hcancel]
        _ = (reesProjChartAlgEquiv (I.map (algebraMap R S))
            (mappedCenterElement (algebraMap R S) I a)) z := hx)

/-- On the embedded original chart, the tensor-product map is the
degree-zero chart map induced by `Proj.map`. -/
theorem reesProjChartBaseChange_one_tmul (I : Ideal R) (a : I)
    (z : reesProjChart I a) :
    reesProjChartBaseChange (S := S) I a ((1 : S) ⊗ₜ[R] z) =
      reesProjChartMap (algebraMap R S) I a z := by
  apply (reesProjChartAlgEquiv (I.map (algebraMap R S))
    (mappedCenterElement (algebraMap R S) I a)).injective
  simp [reesProjChartBaseChange, affineBlowupChartBaseChange,
    affineBlowupChartMapAlgHom, reesProjChartAlgEquiv,
    reesProjChartMap_equiv_comm]

end

section Scheme

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

open AlgebraicGeometry CategoryTheory

attribute [local instance] reesProjChartAlgebra

/-- The zero-degree Rees piece receives the coefficient ring. This is the
base map used by the structural morphism of the blow-up. -/
noncomputable def reesGradeZeroMap (I : Ideal A) : A →+* reesGrade I 0 :=
  { toFun := fun r => ⟨algebraMap A (reesAlgebra I) r, by
      change (⟨monomial 0 r, reesAlgebra.monomial_mem.mpr (by simp)⟩ :
        reesAlgebra I) ∈ reesGrade I 0
      exact reesGrade_monomial_mem I 0 r (by simp)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intro x y; apply Subtype.ext; simp
    map_zero' := by apply Subtype.ext; simp
    map_add' := by intro x y; apply Subtype.ext; simp }

/-- The structural morphism from the Rees Proj blow-up to its affine base. -/
noncomputable def reesProjToSpec (I : Ideal A) :
    reesProj I ⟶ Spec (.of A) :=
  Proj.toSpecZero (reesGrade I) ≫
    Spec.map (CommRingCat.ofHom (reesGradeZeroMap I))

/-- The actual degree-zero Proj chart of the extended center maps to the
relative base change of the original degree-zero chart. -/
noncomputable def reesProjChartBaseChangeSpec (I : Ideal A) (a : I) :
    Spec (.of (reesProjChart (I.map (algebraMap A B))
      (mappedCenterElement (algebraMap A B) I a))) ⟶
      Spec (.of (B ⊗[A] reesProjChart I a)) :=
  Spec.map (CommRingCat.ofHom (reesProjChartBaseChange (S := B) I a).toRingHom)

/-- Every standard Proj chart of the extended blow-up is a closed subscheme
of the corresponding relative base-change chart. -/
instance reesProjChartBaseChangeSpec_isClosedImmersion
    (I : Ideal A) (a : I) :
    IsClosedImmersion (reesProjChartBaseChangeSpec (B := B) I a) := by
  unfold reesProjChartBaseChangeSpec
  exact IsClosedImmersion.spec_of_surjective _
    (reesProjChartBaseChange_surjective (S := B) I a)

#print axioms reesProjChartBaseChange
#print axioms reesProjChartBaseChange_surjective
#print axioms reesProjChartBaseChange_one_tmul
#print axioms reesGradeZeroMap
#print axioms reesProjToSpec
#print axioms reesProjChartBaseChangeSpec
#print axioms reesProjChartBaseChangeSpec_isClosedImmersion

end Scheme

end Pcf.Bounding.AllCodimBlowup
