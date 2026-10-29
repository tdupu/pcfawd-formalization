/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGenericField

/-!
# Fraction-field comparison for a Rees Proj chart

The standard chart `R[I/a]` and the affine base `R` have canonically
equivalent fraction fields. This is the ring-level equivalence needed to
identify the generic stalk map of the Rees Proj structural morphism in
`latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

noncomputable section

variable {R : Type u} [CommRing R] [IsDomain R]

attribute [local instance] reesProjChartAlgebra


/-- The chart fraction field is canonically isomorphic to the fraction field
of its affine base, through their common fraction-field structure over
`R[I/a]`. -/
def affineBlowupChartFractionEquiv (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    FractionRing R ≃+* FractionRing (affineBlowupChart I a) := by
  letI : Algebra (affineBlowupChart I a) (FractionRing R) :=
    (affineBlowupChartToFractionRing I a ha).toRingHom.toAlgebra
  letI : IsFractionRing (affineBlowupChart I a) (FractionRing R) :=
    affineBlowupChart_isFractionRing I a ha
  exact (IsFractionRing.algEquivOfAlgEquiv
    (K := FractionRing R)
    (L := FractionRing (affineBlowupChart I a))
    (AlgEquiv.refl : affineBlowupChart I a ≃ₐ[affineBlowupChart I a]
      affineBlowupChart I a)).toRingEquiv

/-- The fraction-field equivalence carries each base coefficient to its
image in the chart fraction field. -/
theorem affineBlowupChartFractionEquiv_algebraMap (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) (r : R) :
    affineBlowupChartFractionEquiv I a ha (algebraMap R (FractionRing R) r) =
      algebraMap (affineBlowupChart I a)
        (FractionRing (affineBlowupChart I a))
          (algebraMap R (affineBlowupChart I a) r) := by
  letI : Algebra (affineBlowupChart I a) (FractionRing R) :=
    (affineBlowupChartToFractionRing I a ha).toRingHom.toAlgebra
  letI : IsFractionRing (affineBlowupChart I a) (FractionRing R) :=
    affineBlowupChart_isFractionRing I a ha
  have h : (algebraMap (affineBlowupChart I a) (FractionRing R))
      (algebraMap R (affineBlowupChart I a) r) =
        algebraMap R (FractionRing R) r :=
    (affineBlowupChartToFractionRing I a ha).commutes r
  rw [← h]
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (K := FractionRing R)
    (L := FractionRing (affineBlowupChart I a))
    (AlgEquiv.refl : affineBlowupChart I a ≃ₐ[affineBlowupChart I a]
      affineBlowupChart I a)
    (algebraMap R (affineBlowupChart I a) r)

/-- The affine base embeds in the actual degree-zero Rees Proj chart when its
distinguished centre coordinate is nonzero. -/
theorem algebraMap_reesProjChart_injective (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    Function.Injective ((reesProjChartAlgEquiv I a).symm.toRingHom.comp
      (algebraMap R (affineBlowupChart I a))) := by
  have hloc : Function.Injective (algebraMap R (Localization.Away (a : R))) :=
    IsLocalization.injective (Localization.Away (a : R))
      (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hchart : Function.Injective (algebraMap R (affineBlowupChart I a)) := by
    intro x y h
    apply hloc
    exact congrArg Subtype.val h
  exact (reesProjChartAlgEquiv I a).symm.injective.comp hchart

/-- A Rees Proj with nonzero centre is dominant over its affine base. This is
the scheme-level generic-point input for the function-field comparison. -/
theorem reesProjToSpec_isDominant (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) : IsDominant (reesProjToSpec I) := by
  letI : Algebra R (reesProjChart I a) := reesProjChartAlgebra I a
  have hchart : IsDominant
      (reesProjChartOpen I a ≫ reesProjToSpec I) := by
    rw [reesProjChartOpen_toSpec_alg]
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap
      ((reesProjChartAlgEquiv I a).symm.toRingHom.comp
        (algebraMap R (affineBlowupChart I a))))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
      ((reesProjChartAlgEquiv I a).symm.toRingHom.comp
        (algebraMap R (affineBlowupChart I a)))).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (algebraMap_reesProjChart_injective I a ha)]
    exact bot_le
  letI : IsDominant (reesProjChartOpen I a ≫ reesProjToSpec I) := hchart
  exact IsDominant.of_comp (reesProjChartOpen I a) (reesProjToSpec I)

/-- The generic point of the actual Rees Proj maps to the generic point of
the affine base. -/
theorem reesProjToSpec_genericPoint (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    reesProjToSpec I (genericPoint (reesProj I)) =
      genericPoint (Spec (.of R)) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsDominant (reesProjToSpec I) :=
    reesProjToSpec_isDominant I a ha
  exact map_genericPoint_eq_of_isDominant (reesProjToSpec I)

#print axioms affineBlowupChartFractionEquiv
#print axioms affineBlowupChartFractionEquiv_algebraMap
#print axioms algebraMap_reesProjChart_injective
#print axioms reesProjToSpec_isDominant
#print axioms reesProjToSpec_genericPoint

end

end Pcf.Bounding.AllCodimBlowup
