/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupNormalizedCartier
public import Pcf.Bounding.GlobalNormalization
public import Pcf.Stacks.Abhyankar.Scheme.NormalizationChart

/-!
# Affine standard opens of the absolute normalized Rees blow-up

The inverse image of a standard affine blow-up chart under absolute
normalization is affine. Its ring of sections is the integral closure of the
ordinary chart ring in the function-field sections. This identifies the
scheme-theoretic neighborhood on which the exceptional equation from
`AllCodimBlowupNormalizedCartier` must be transported.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsDomain R]

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The actual standard affine open in the Rees `Proj`. -/
def reesProjStandardOpen (I : Ideal R) (a : I) : (reesProj I).Opens :=
  (reesProjChartOpen I a).opensRange

/-- Every standard Rees `Proj` open is affine. -/
theorem reesProjStandardOpen_isAffine (I : Ideal R) (a : I) :
    IsAffineOpen (reesProjStandardOpen I a) :=
  isAffineOpen_opensRange (reesProjChartOpen I a)

/-- Sections of the actual standard open are its degree-zero homogeneous
localization ring. -/
def reesProjStandardOpen_sectionsIso (I : Ideal R) (a : I) :
    Γ(reesProj I, reesProjStandardOpen I a) ≅ .of (reesProjChart I a) :=
  (IsOpenImmersion.ΓIsoTop (reesProjChartOpen I a)).symm ≪≫
    Scheme.ΓSpecIso (.of (reesProjChart I a))

/-- A standard chart indexed by a nonzero centre element is nonempty. -/
theorem reesProjStandardOpen_nonempty
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    Nonempty (reesProjStandardOpen I a) := by
  letI : IsDomain (reesProjChart I a) :=
    reesProjChart_isDomain_of_nonzero I a ha
  let η := genericPoint (Spec (.of (reesProjChart I a)))
  refine ⟨⟨reesProjChartOpen I a η, ?_⟩⟩
  change reesProjChartOpen I a η ∈ (reesProjChartOpen I a).opensRange
  exact ⟨η, rfl⟩

/-- The inverse image of a standard Rees chart under absolute
normalization is an affine open of the normalized blow-up. -/
theorem normalizedReesProjStandardOpen_isAffine
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    IsAffineOpen ((Palomar.normalizationMap (reesProj I)) ⁻¹ᵁ
      reesProjStandardOpen I a) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  exact (reesProjStandardOpen_isAffine I a).preimage
    (Palomar.normalizationMap (reesProj I))

/-- On the actual inverse standard open of the absolute normalization,
sections are the integral closure of the standard-open section ring in the
generic-point sections. -/
def normalizedReesProjStandardOpen_sections
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let X := reesProj I
    let U := reesProjStandardOpen I a
    let g := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, U) Γ(Spec X.functionField, g ⁻¹ᵁ U) :=
      (g.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(Palomar.normalization X,
      (Palomar.normalizationMap X) ⁻¹ᵁ U) :=
      ((Palomar.normalizationMap X).app U).hom.toAlgebra
    Γ(Palomar.normalization X, (Palomar.normalizationMap X) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) Γ(Spec X.functionField, g ⁻¹ᵁ U) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let X := reesProj I
  let U := reesProjStandardOpen I a
  exact Pcf.Stacks.SchemeLevel.normalizationAppAlgEquiv
    (Pcf.schemeGenericInclusion X) (reesProjStandardOpen_isAffine I a)

#print axioms reesProjStandardOpen_isAffine
#print axioms reesProjStandardOpen_sectionsIso
#print axioms reesProjStandardOpen_nonempty
#print axioms normalizedReesProjStandardOpen_isAffine
#print axioms normalizedReesProjStandardOpen_sections

end
end Pcf.Bounding.AllCodimBlowup
