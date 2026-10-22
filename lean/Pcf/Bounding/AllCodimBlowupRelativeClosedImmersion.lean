/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupDegreeOneCover

/-!
# Relative closed immersion of Rees Proj

The relative comparison is a closed immersion on every degree-one standard
affine chart. This file identifies the chart structural map with the map
used in the scheme fibre product and constructs the chartwise closed immersion.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] reesProjChartAlgebra

/-- The degree-zero chart equivalence carries the base-ring map to the
usual structural map of the explicit affine blow-up chart. -/
theorem reesProjChartEquiv_zeroMap (I : Ideal R) (a : I) (r : R) :
    reesProjChartEquiv I a
      (HomogeneousLocalization.fromZeroRingHom (reesGrade I)
        (Submonoid.powers (reesDegreeOne I a)) (reesGradeZeroMap I r)) =
      algebraMap R (affineBlowupChart I a) r := by
  apply Subtype.ext
  change reesProjChartEval I a
    (HomogeneousLocalization.fromZeroRingHom (reesGrade I)
      (Submonoid.powers (reesDegreeOne I a)) (reesGradeZeroMap I r)) =
    algebraMap R (Localization.Away a.1) r
  have hzero :
      HomogeneousLocalization.fromZeroRingHom (reesGrade I)
        (Submonoid.powers (reesDegreeOne I a)) (reesGradeZeroMap I r) =
      HomogeneousLocalization.Away.mk (reesGrade I)
        (reesDegreeOne_mem_grade I a) 0 (reesGradeZeroMap I r).1
        (by exact (reesGradeZeroMap I r).2) := rfl
  rw [hzero, reesProjChartEval_mk]
  simp [reesGradeZeroMap, reesChartEval]

/-- The standard Proj open's structural morphism is the spectrum of the
transported `R`-algebra structure on its degree-zero chart. -/
theorem reesProjChartOpen_toSpec_alg (I : Ideal R) (a : I) :
    reesProjChartOpen I a ≫ reesProjToSpec I =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (reesProjChart I a))) := by
  rw [reesProjChartOpen_toSpec]
  congr 1
  congr 1
  apply RingHom.ext
  intro r
  apply (reesProjChartEquiv I a).injective
  change reesProjChartEquiv I a
      (HomogeneousLocalization.fromZeroRingHom (reesGrade I)
        (Submonoid.powers (reesDegreeOne I a)) (reesGradeZeroMap I r)) =
    reesProjChartEquiv I a
      ((reesProjChartEquiv I a).symm
        (algebraMap R (affineBlowupChart I a) r))
  rw [RingEquiv.apply_symm_apply]
  exact reesProjChartEquiv_zeroMap I a r

/-- The base change of a standard Proj chart over the affine base is the
affine scheme of its tensor-product coordinate ring. -/
noncomputable def reesProjChartPullbackIso (I : Ideal R) (a : I) :
    Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reesProjChartOpen I a ≫ reesProjToSpec I) ≅
        Spec (.of (S ⊗[R] reesProjChart I a)) := by
  rw [reesProjChartOpen_toSpec_alg]
  exact pullbackSpecIso R S (reesProjChart I a)

/-- The relative comparison restricted to a standard degree-one Proj chart,
as a morphism to the affine chart's actual fibre product. -/
noncomputable def reesProjChartRelativeBaseChange (I : Ideal R) (a : I) :
    Spec (.of (reesProjChart (I.map (algebraMap R S))
      (mappedCenterElement (algebraMap R S) I a))) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) :=
  Limits.pullback.lift
    (reesProjChartOpen (I.map (algebraMap R S))
      (mappedCenterElement (algebraMap R S) I a) ≫
        reesProjToSpec (I.map (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom
      (reesProjChartMap (algebraMap R S) I a)))
    (reesProjChartMap_toSpec (algebraMap R S) I a).symm

theorem reesProjChartRelativeBaseChange_fst (I : Ideal R) (a : I) :
    reesProjChartRelativeBaseChange (S := S) I a ≫
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) =
      reesProjChartOpen (I.map (algebraMap R S))
        (mappedCenterElement (algebraMap R S) I a) ≫
          reesProjToSpec (I.map (algebraMap R S)) :=
  Limits.pullback.lift_fst ..

theorem reesProjChartRelativeBaseChange_snd (I : Ideal R) (a : I) :
    reesProjChartRelativeBaseChange (S := S) I a ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) =
      Spec.map (CommRingCat.ofHom
        (reesProjChartMap (algebraMap R S) I a)) :=
  Limits.pullback.lift_snd ..

/-- The explicit surjective tensor-product chart map gives a closed
immersion into the actual scheme fibre product. -/
noncomputable def reesProjChartRelativeClosedImmersion (I : Ideal R) (a : I) :
    Spec (.of (reesProjChart (I.map (algebraMap R S))
      (mappedCenterElement (algebraMap R S) I a))) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) :=
  reesProjChartBaseChangeSpec (B := S) I a ≫
    (reesProjChartPullbackIso (S := S) I a).inv

instance reesProjChartRelativeClosedImmersion_isClosedImmersion
    (I : Ideal R) (a : I) :
    IsClosedImmersion (reesProjChartRelativeClosedImmersion (S := S) I a) := by
  unfold reesProjChartRelativeClosedImmersion
  infer_instance

#print axioms reesProjChartEquiv_zeroMap
#print axioms reesProjChartOpen_toSpec_alg
#print axioms reesProjChartPullbackIso
#print axioms reesProjChartRelativeBaseChange
#print axioms reesProjChartRelativeBaseChange_fst
#print axioms reesProjChartRelativeBaseChange_snd
#print axioms reesProjChartRelativeClosedImmersion
#print axioms reesProjChartRelativeClosedImmersion_isClosedImmersion

end Pcf.Bounding.AllCodimBlowup
