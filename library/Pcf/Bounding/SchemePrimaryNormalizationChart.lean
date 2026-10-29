/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryLocalDeltaConstant
public import Pcf.Bounding.GlobalNormalizationFinite

/-!
# Affine charts of normalization in a field extension

For an integral scheme `X` and an extension `L / X.functionField`,
the relative normalization of the composite generic inclusion
`Spec L ⟶ X` is the actual normalization of `X` in `L`.
This file identifies the source sections over a nonempty affine chart
with `L`, the normalization chart with an integral closure, and every
normalization stalk with a localization of that closure. This supplies
the global chart input for `paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

variable (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]

/-- The actual map from the extension field's generic point to `X`. -/
def schemeFieldExtensionInclusion : Spec (.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
    schemeGenericInclusion X

/-- Every nonempty open of `X` contains the image of the sole point of
`Spec L`, so its inverse image is all of `Spec L`. -/
theorem schemeFieldExtensionInclusion_preimage_eq_top
    (U : X.Opens) [Nonempty U] :
    schemeFieldExtensionInclusion X L ⁻¹ᵁ U = ⊤ := by
  rw [schemeFieldExtensionInclusion, Scheme.Hom.comp_preimage,
    schemeGenericInclusion_preimage_eq_top]
  simp

/-- The sections above a nonempty open under the extension-field
generic inclusion are canonically the extension field. -/
def schemeFieldExtensionSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec (.of L), schemeFieldExtensionInclusion X L ⁻¹ᵁ U) ≅ .of L :=
  (Spec (.of L)).presheaf.mapIso
    (eqToIso (schemeFieldExtensionInclusion_preimage_eq_top X L U).symm).op ≪≫
    Scheme.ΓSpecIso (.of L)

/-- The field-sections identification respects the coordinate ring of `X`.
This is the algebra structure used in the affine normalization chart. -/
def schemeFieldExtensionSectionsAlgEquiv
    (U : X.Opens) [Nonempty U] :
    letI := ((schemeFieldExtensionInclusion X L).app U).hom.toAlgebra
    letI := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    Γ(Spec (.of L), schemeFieldExtensionInclusion X L ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] L := by
  let f := schemeFieldExtensionInclusion X L
  let : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  let e := schemeFieldExtensionSectionsIso X L U
  have he : f.app U ≫ e.hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
    have hgeneric : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
    have hmem : f (IsLocalRing.closedPoint L) ∈ U := by
      have h : IsLocalRing.closedPoint L ∈ f ⁻¹ᵁ U := by
        rw [show f ⁻¹ᵁ U = ⊤ from schemeFieldExtensionInclusion_preimage_eq_top X L U]
        trivial
      exact h
    calc
      f.app U ≫ e.hom =
          X.presheaf.germ U _ hmem ≫ Scheme.stalkClosedPointTo f := by
        simpa only [f, e, schemeFieldExtensionSectionsIso] using
          (Scheme.germ_stalkClosedPointTo (f := f) U hmem).symm
      _ = X.germToFunctionField U ≫
          CommRingCat.ofHom (algebraMap X.functionField L) := by
        exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
          (CommRingCat.ofHom (algebraMap X.functionField L)) U hmem
  exact { e.commRingCatIsoToRingEquiv with
    commutes' r := congr($(he) r) }

/-- The affine chart of the actual relative normalization is the
integral closure of the chart ring in the extension-field sections. -/
def schemeFieldExtensionNormalizationChartIso
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := ((schemeFieldExtensionInclusion X L).app U).hom.toAlgebra
    Γ((schemeFieldExtensionInclusion X L).normalization,
      (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(X, U)
        Γ(Spec (.of L), schemeFieldExtensionInclusion X L ⁻¹ᵁ U)) :=
  (schemeFieldExtensionInclusion X L).normalizationObjIso hU

/-- The affine coordinate ring of the relative normalization is the actual
integral closure of the base chart ring *inside* the chosen field extension. -/
def schemeFieldExtensionNormalizationIntegralClosureEquiv
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((schemeFieldExtensionInclusion X L).app U).hom.toAlgebra
    letI := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    Γ((schemeFieldExtensionInclusion X L).normalization,
      (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ U) ≃+*
      integralClosure Γ(X, U) L := by
  let f := schemeFieldExtensionInclusion X L
  let : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  exact (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.trans
    (schemeFieldExtensionSectionsAlgEquiv X L U).mapIntegralClosure.toRingEquiv

/-- A stalk of the actual relative normalization is a localization of the
integral closure in `L` at the prime transported from its affine chart. -/
theorem schemeFieldExtensionNormalizationStalk_isLocalization
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (y : (schemeFieldExtensionInclusion X L).normalization)
    (hy : y ∈ (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ U) :
    let f := schemeFieldExtensionInclusion X L
    let V := f.fromNormalization ⁻¹ᵁ U
    let hV : IsAffineOpen V := hU.preimage f.fromNormalization
    let yV : V := ⟨y, hy⟩
    letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    let e := schemeFieldExtensionNormalizationIntegralClosureEquiv X L U hU
    let q := (hV.primeIdealOf yV).asIdeal
    letI : Algebra (integralClosure Γ(X, U) L)
        (f.normalization.presheaf.stalk (yV : f.normalization)) :=
      ((f.normalization.presheaf.germ V y hy).hom.comp
        e.symm.toRingHom).toAlgebra
    IsLocalization (q.primeCompl.map e)
      (f.normalization.presheaf.stalk (yV : f.normalization)) := by
  let f := schemeFieldExtensionInclusion X L
  let V := f.fromNormalization ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f.fromNormalization
  let yV : V := ⟨y, hy⟩
  letI : Algebra Γ(X, U) Γ(Spec (.of L), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  let e := schemeFieldExtensionNormalizationIntegralClosureEquiv X L U hU
  let q := (hV.primeIdealOf yV).asIdeal
  letI : Algebra Γ(f.normalization, V)
      (f.normalization.presheaf.stalk (yV : f.normalization)) :=
    f.normalization.presheaf.algebra_section_stalk yV
  letI : IsLocalization.AtPrime
      (f.normalization.presheaf.stalk (yV : f.normalization)) q :=
    hV.isLocalization_stalk yV
  letI : Algebra (integralClosure Γ(X, U) L)
      (f.normalization.presheaf.stalk (yV : f.normalization)) :=
    ((algebraMap Γ(f.normalization, V)
      (f.normalization.presheaf.stalk (yV : f.normalization))).comp
      e.symm.toRingHom).toAlgebra
  exact IsLocalization.isLocalization_of_base_ringEquiv q.primeCompl
    (f.normalization.presheaf.stalk (yV : f.normalization)) e

#print axioms schemeFieldExtensionInclusion_preimage_eq_top
#print axioms schemeFieldExtensionSectionsIso
#print axioms schemeFieldExtensionSectionsAlgEquiv
#print axioms schemeFieldExtensionNormalizationChartIso
#print axioms schemeFieldExtensionNormalizationIntegralClosureEquiv
#print axioms schemeFieldExtensionNormalizationStalk_isLocalization

end
end Pcf
