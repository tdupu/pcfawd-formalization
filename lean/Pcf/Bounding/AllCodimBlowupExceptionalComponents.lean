/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupNormalizedExceptional
public import Pcf.Bounding.GlobalNormalizationMorphism
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finiteness of exceptional components on an absolute normalized blow-up

For a finitely generated nonzero centre in an integral affine variety,
the Rees blow-up and its finite absolute normalization are Noetherian.
Consequently the actual exceptional support has finitely many irreducible
components. This is the finite family appearing at the start of the proof
of `latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

omit [IsDomain R] in
/-- The blow-up of a finitely generated centre in an affine variety is a
Noetherian topological space. -/
theorem reesProj_noetherianSpace (k : Type u) [Field k]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) :
    NoetherianSpace (reesProj I) := by
  change NoetherianSpace (Proj (reesGrade I))
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsNoetherianRing (reesGrade I 0) :=
    isNoetherianRing_of_surjective R (reesGrade I 0)
      (reesGradeZeroMap I) (reesGradeZeroMap_surjective I)
  haveI : Algebra.FiniteType (reesGrade I 0) (reesAlgebra I) :=
    reesAlgebra_finiteType_over_zeroGrade I hI
  haveI : LocallyOfFiniteType (Proj.toSpecZero (reesGrade I)) := inferInstance
  haveI : IsProper (Proj.toSpecZero (reesGrade I)) := inferInstance
  letI : CompactSpace (Proj (reesGrade I)) :=
    QuasiCompact.compactSpace_of_compactSpace
      (Proj.toSpecZero (reesGrade I))
  letI : IsLocallyNoetherian (Proj (reesGrade I)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Proj.toSpecZero (reesGrade I))
  letI : IsNoetherian (Proj (reesGrade I)) := {}
  infer_instance

/-- The finite absolute normalization of the blow-up is Noetherian. -/
theorem normalizedReesProj_noetherianSpace (k : Type u) [Field k]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG)
    (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    NoetherianSpace (Palomar.normalization (reesProj I)) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : NoetherianSpace (reesProj I) := reesProj_noetherianSpace k I hI
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
    reesProjToSpecField_locallyOfFiniteType k I hI
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (reesProjToSpecField (k := k) I)
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  infer_instance

/-- The exceptional support on the actual normalized blow-up has a finite
set of irreducible components. -/
theorem normalizedReesExceptional_finite_components
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    (irreducibleComponents
      ((normalizedReesExceptionalIdealSheaf I a ha).support :
        Set (Palomar.normalization (reesProj I)))).Finite := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : NoetherianSpace (Palomar.normalization (reesProj I)) :=
    normalizedReesProj_noetherianSpace k I hI a ha
  exact NoetherianSpace.finite_irreducibleComponents

#print axioms reesProj_noetherianSpace
#print axioms normalizedReesProj_noetherianSpace
#print axioms normalizedReesExceptional_finite_components

end
end Pcf.Bounding.AllCodimBlowup
