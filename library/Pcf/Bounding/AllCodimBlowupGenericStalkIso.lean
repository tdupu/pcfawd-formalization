/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGenericStalkNaturality
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Generic stalk of the Rees blow-up structure morphism

The standard affine Rees chart has the same fraction field as its integral
affine base. We compare the corresponding scheme generic stalk map to this
field equivalence, for the birationality assertion in
`latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

noncomputable section

variable {R : Type u} [CommRing R] [IsDomain R]


noncomputable local instance affineBaseFunctionFieldAlgebra :
    Algebra R (Spec (.of R)).functionField :=
  RingHom.toAlgebra (StructureSheaf.toStalk (CommRingCat.of R)
    (genericPoint (Spec (.of R)))).hom

noncomputable local instance affineBaseFunctionFieldIsFractionRing :
    IsFractionRing R (Spec (.of R)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine
    (CommRingCat.of R)

attribute [local instance] reesProjChartAlgebra

theorem reesProjChart_isDomain_of_nonzero (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) : IsDomain (reesProjChart I a) := by
  letI : IsDomain (affineBlowupChart I a) :=
    affineBlowupChart_isDomain_of_nonzero I a ha
  exact (reesProjChartAlgEquiv I a).toMulEquiv.isDomain _

/-- Fraction-field equivalence for the actual degree-zero Rees Proj chart. -/
def affineBaseReesChartFractionEquiv (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    FractionRing R ≃+* FractionRing (reesProjChart I a) :=
  (affineBlowupChartFractionEquiv I a ha).trans
    (IsFractionRing.ringEquivOfRingEquiv
      (reesProjChartAlgEquiv I a).symm.toRingEquiv)

/-- Compatibility of the fraction-field equivalence with coefficients. -/
theorem affineBaseReesChartFractionEquiv_algebraMap
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) (r : R) :
    letI : Algebra R (reesProjChart I a) := reesProjChartAlgebra I a
    letI : Algebra (reesProjChart I a) (FractionRing (reesProjChart I a)) :=
      inferInstance
    affineBaseReesChartFractionEquiv I a ha
        (algebraMap R (FractionRing R) r) =
      (@algebraMap (reesProjChart I a) (FractionRing (reesProjChart I a))
        _ _ (inferInstance : Algebra (reesProjChart I a)
          (FractionRing (reesProjChart I a))))
        ((reesProjChartAlgEquiv I a).symm
          (algebraMap R (affineBlowupChart I a) r)) := by
  letI : Algebra R (reesProjChart I a) := reesProjChartAlgebra I a
  letI : Algebra (reesProjChart I a) (FractionRing (reesProjChart I a)) :=
    inferInstance
  unfold affineBaseReesChartFractionEquiv
  rw [RingEquiv.trans_apply,
    affineBlowupChartFractionEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- The affine base and an actual degree-zero Rees Proj chart have
isomorphic scheme function fields. -/
def affineBaseReesChartFunctionFieldEquiv (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    letI : IsDomain (reesProjChart I a) :=
      reesProjChart_isDomain_of_nonzero I a ha
    (Spec (.of R)).functionField ≃+*
      (Spec (.of (reesProjChart I a))).functionField := by
  letI : IsDomain (reesProjChart I a) :=
    reesProjChart_isDomain_of_nonzero I a ha
  letI : IsIntegral (Spec (.of (reesProjChart I a))) := inferInstance
  letI : Algebra (reesProjChart I a)
      (Spec (.of (reesProjChart I a))).functionField :=
    RingHom.toAlgebra (StructureSheaf.toStalk
      (CommRingCat.of (reesProjChart I a))
      (genericPoint (Spec (.of (reesProjChart I a))))).hom
  letI : IsFractionRing (reesProjChart I a)
      (Spec (.of (reesProjChart I a))).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine
      (CommRingCat.of (reesProjChart I a))
  exact (FractionRing.algEquiv (A := R) (Spec (.of R)).functionField).symm.toRingEquiv |>.trans
    (affineBaseReesChartFractionEquiv I a ha) |>.trans
      (FractionRing.algEquiv (A := reesProjChart I a)
        (Spec (.of (reesProjChart I a))).functionField).toRingEquiv

/-- The scheme function-field equivalence sends base coefficients to their
images in the Proj chart. -/
theorem affineBaseReesChartFunctionFieldEquiv_base
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) (r : R) :
    letI : IsDomain (reesProjChart I a) :=
      reesProjChart_isDomain_of_nonzero I a ha
    affineBaseReesChartFunctionFieldEquiv I a ha
        ((StructureSheaf.toStalk (CommRingCat.of R)
          (genericPoint (Spec (.of R)))).hom r) =
      (StructureSheaf.toStalk (CommRingCat.of (reesProjChart I a))
        (genericPoint (Spec (.of (reesProjChart I a))))).hom
          ((reesProjChartAlgEquiv I a).symm
            (algebraMap R (affineBlowupChart I a) r)) := by
  letI : IsDomain (reesProjChart I a) :=
    reesProjChart_isDomain_of_nonzero I a ha
  letI : Algebra (reesProjChart I a)
      (Spec (.of (reesProjChart I a))).functionField :=
    RingHom.toAlgebra (StructureSheaf.toStalk
      (CommRingCat.of (reesProjChart I a))
      (genericPoint (Spec (.of (reesProjChart I a))))).hom
  letI : IsFractionRing (reesProjChart I a)
      (Spec (.of (reesProjChart I a))).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine
      (CommRingCat.of (reesProjChart I a))
  change (FractionRing.algEquiv (A := reesProjChart I a)
        (Spec (.of (reesProjChart I a))).functionField).toRingEquiv
      ((affineBaseReesChartFractionEquiv I a ha)
        ((FractionRing.algEquiv (A := R)
          (Spec (.of R)).functionField).symm.toRingEquiv
            (algebraMap R (Spec (.of R)).functionField r))) =
      algebraMap (reesProjChart I a)
        (Spec (.of (reesProjChart I a))).functionField
          ((reesProjChartAlgEquiv I a).symm
            (algebraMap R (affineBlowupChart I a) r))
  rw [show (FractionRing.algEquiv (A := R)
      (Spec (.of R)).functionField).symm.toRingEquiv
        (algebraMap R (Spec (.of R)).functionField r) =
      algebraMap R (FractionRing R) r from by
        apply (FractionRing.algEquiv (A := R)
          (Spec (.of R)).functionField).injective
        change (FractionRing.algEquiv (A := R)
          (Spec (.of R)).functionField)
            ((FractionRing.algEquiv (A := R)
              (Spec (.of R)).functionField).symm
                (algebraMap R (Spec (.of R)).functionField r)) = _
        rw [AlgEquiv.apply_symm_apply]
        exact ((FractionRing.algEquiv (A := R)
          (Spec (.of R)).functionField).commutes r).symm]
  rw [affineBaseReesChartFractionEquiv_algebraMap]
  exact (FractionRing.algEquiv (A := reesProjChart I a)
    (Spec (.of (reesProjChart I a))).functionField).commutes _

#print axioms affineBaseReesChartFractionEquiv
#print axioms affineBaseReesChartFractionEquiv_algebraMap
#print axioms affineBaseReesChartFunctionFieldEquiv
#print axioms affineBaseReesChartFunctionFieldEquiv_base

end

end Pcf.Bounding.AllCodimBlowup
