/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupAbsoluteNormalization
public import Pcf.Bounding.AllCodimBlowupExceptionalProjChart
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Exceptional centre on the normalized Rees blow-up

This module constructs the actual pullback ideal sheaf defining the inverse
image of the blow-up centre on the absolute normalization and identifies its
support.  This is the exceptional divisor support in the proof of
`latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

variable {R : Type u} [CommRing R]

set_option linter.style.haveILetI false

/-- The ideal sheaf on the affine base associated to the centre ideal `I`. -/
def affineCenterIdealSheaf (I : Ideal R) : (Spec (.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The affine centre sheaf has exactly the underlying closed subset `V(I)`. -/
theorem affineCenterIdealSheaf_support (I : Ideal R) :
    ((affineCenterIdealSheaf I).support : Set (Spec (.of R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  change (Spec (.of R)).zeroLocus
    ((I.map (Scheme.ΓSpecIso (.of R)).inv.hom) :
      Set Γ(Spec (.of R), ⊤)) = _
  rw [Spec_zeroLocus, ← Ideal.coe_comap]
  rw [Ideal.comap_map_of_bijective (Scheme.ΓSpecIso (.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso _)]

/-- The actual pulled-back centre ideal sheaf on the Rees blow-up. -/
def reesExceptionalIdealSheaf (I : Ideal R) : (reesProj I).IdealSheafData :=
  (affineCenterIdealSheaf I).comap (reesProjToSpec I)

/-- The actual pulled-back centre ideal sheaf on the absolute normalization
of the Rees blow-up. -/
def normalizedReesExceptionalIdealSheaf [IsDomain R] (I : Ideal R)
    (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    (Palomar.normalization (reesProj I)).IdealSheafData := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  exact (reesExceptionalIdealSheaf I).comap (Palomar.normalizationMap (reesProj I))

/-- The support of the normalized exceptional centre is the full inverse
image of the original centre, including every exceptional component. -/
theorem normalizedReesExceptionalIdealSheaf_support [IsDomain R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    ((normalizedReesExceptionalIdealSheaf I a ha).support :
      Set (Palomar.normalization (reesProj I))) =
      (Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I).base ⁻¹'
        PrimeSpectrum.zeroLocus (I : Set R) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  rw [normalizedReesExceptionalIdealSheaf,
    Scheme.IdealSheafData.support_comap,
    reesExceptionalIdealSheaf,
    Scheme.IdealSheafData.support_comap]
  change (Palomar.normalizationMap (reesProj I)).base ⁻¹'
    ((reesProjToSpec I).base ⁻¹'
      ((affineCenterIdealSheaf I).support : Set (Spec (.of R)))) = _
  rw [affineCenterIdealSheaf_support]
  rfl

#print axioms affineCenterIdealSheaf
#print axioms affineCenterIdealSheaf_support
#print axioms reesExceptionalIdealSheaf
#print axioms normalizedReesExceptionalIdealSheaf
#print axioms normalizedReesExceptionalIdealSheaf_support

end

end Pcf.Bounding.AllCodimBlowup
