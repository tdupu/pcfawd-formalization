/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalization
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Normality of the canonical global normalization

We identify the inverse image of each nonempty affine open with the spectrum
of its integral closure in the function field, then pass through stalks to all
affine opens of the normalization.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

variable (A : Scheme.{u}) [IsIntegral A]

/-- The generic point lies in every nonempty open of an integral scheme. -/
theorem schemeGenericInclusion_preimage_eq_top (U : A.Opens) [Nonempty U] :
    schemeGenericInclusion A ⁻¹ᵁ U = ⊤ := by
  let : Subsingleton (Spec A.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum A.functionField))
  apply le_antisymm le_top
  intro x _
  have hx : x = IsLocalRing.closedPoint A.functionField := Subsingleton.elim _ _
  subst x
  change A.fromSpecStalk (genericPoint A) _ ∈ U
  rw [A.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec A).mem_open_set_iff U.isOpen).mpr (by
    simpa using (inferInstance : Nonempty U))

/-- The sections over the generic preimage of a nonempty open are the function field. -/
def schemeGenericInclusionSectionsIso (U : A.Opens) [Nonempty U] :
    Γ(Spec A.functionField, schemeGenericInclusion A ⁻¹ᵁ U) ≅ A.functionField :=
  (Spec A.functionField).presheaf.mapIso
    (eqToIso (schemeGenericInclusion_preimage_eq_top A U).symm).op ≪≫
      Scheme.ΓSpecIso _

/-- The coordinate rings on inverse images of nonempty affine opens are normal. -/
theorem schemeGlobalNormalization_preimage_integrallyClosed
    (U : A.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(Palomar.normalization A,
      Palomar.normalizationMap A ⁻¹ᵁ U) := by
  let R := Γ(A, U)
  let S := Γ(Spec A.functionField, schemeGenericInclusion A ⁻¹ᵁ U)
  let : Algebra R S := ((schemeGenericInclusion A).app U).hom.toAlgebra
  let e : S ≃+* A.functionField :=
    (schemeGenericInclusionSectionsIso A U).commRingCatIsoToRingEquiv
  let : IsDomain S := e.toMulEquiv.isDomain _
  let : IsIntegrallyClosed S := IsIntegrallyClosed.of_equiv e.symm
  let : IsIntegrallyClosed (integralClosure R S) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
      (integralClosure R S) S
  exact IsIntegrallyClosed.of_equiv
    ((schemeGenericInclusion A).normalizationObjIso hU).symm.commRingCatIsoToRingEquiv

/-- Every local ring of the canonical normalization is integrally closed. -/
theorem schemeGlobalNormalization_stalk_integrallyClosed
    (x : Palomar.normalization A) :
    IsIntegrallyClosed ((Palomar.normalization A).presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show Palomar.normalizationMap A x ∈ (⊤ : A.Opens) from trivial)
  let : Nonempty U := ⟨⟨_, hxU⟩⟩
  let V := Palomar.normalizationMap A ⁻¹ᵁ U
  let xV : V := ⟨x, hxU⟩
  have hV : IsAffineOpen V := hU.preimage (Palomar.normalizationMap A)
  let : Nonempty V := ⟨xV⟩
  let : IsIntegrallyClosed Γ(Palomar.normalization A, V) :=
    schemeGlobalNormalization_preimage_integrallyClosed A U hU
  let : Algebra Γ(Palomar.normalization A, V)
      ((Palomar.normalization A).presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk _ xV
  let : IsLocalization.AtPrime ((Palomar.normalization A).presheaf.stalk x)
      (hV.primeIdealOf xV).asIdeal := hV.isLocalization_stalk xV
  exact isIntegrallyClosed_of_isLocalization _ _
    (hV.primeIdealOf xV).asIdeal.primeCompl_le_nonZeroDivisors

/-- On an integral scheme, normality of every stalk implies normality of every
affine coordinate ring. -/
theorem isNormalScheme_of_stalk_integrallyClosed (X : Scheme.{u}) [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsNormalScheme X := by
  classical
  constructor
  intro U
  by_cases hU : Nonempty (U : X.Opens)
  · let : Nonempty (U : X.Opens) := hU
    let (P : Ideal Γ(X, U)) [hP : P.IsPrime] :
        Algebra Γ(X, U) (X.presheaf.stalk (U.2.fromSpec ⟨P, hP⟩)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf
        ⟨U.2.fromSpec ⟨P, hP⟩, (U.2.isoSpec.inv ⟨P, hP⟩).2⟩
    let (P : Ideal Γ(X, U)) [hP : P.IsPrime] :
        IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec ⟨P, hP⟩)) P :=
      U.2.isLocalization_stalk' ⟨P, hP⟩ (U.2.isoSpec.inv ⟨P, hP⟩).2
    exact IsIntegrallyClosed.of_isLocalization_maximal
      (fun P hP ↦ X.presheaf.stalk (U.2.fromSpec ⟨P, hP.isPrime⟩))
      (fun P hP ↦ h (U.2.fromSpec ⟨P, hP.isPrime⟩))
  · let : Subsingleton Γ(X, U) := PrimeSpectrum.isEmpty_iff_subsingleton.mp
      ⟨fun p ↦ hU ⟨U.2.isoSpec.inv p⟩⟩
    apply (isIntegrallyClosed_iff (FractionRing Γ(X, U))).mpr
    intro x _
    exact ⟨0, Subsingleton.elim _ _⟩

/-- The canonical global normalization is normal in the affine-coordinate
sense used by the divisor bridge. -/
instance schemeGlobalNormalization_isNormal : IsNormalScheme (Palomar.normalization A) :=
  isNormalScheme_of_stalk_integrallyClosed (Palomar.normalization A)
    (schemeGlobalNormalization_stalk_integrallyClosed A)

#print axioms schemeGenericInclusion_preimage_eq_top
#print axioms schemeGenericInclusionSectionsIso
#print axioms schemeGlobalNormalization_preimage_integrallyClosed
#print axioms schemeGlobalNormalization_stalk_integrallyClosed
#print axioms isNormalScheme_of_stalk_integrallyClosed
#print axioms schemeGlobalNormalization_isNormal

end

end Pcf
