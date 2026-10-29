/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.Cusp
public import Pcf.Bounding.ReducedFiberBranch
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Affine normalization geometry for `paper.tex`, Example `ex:cusp`

The cusp is represented here by the actual subalgebra `k[t²,t³]` of `k[t]`.
The parametrization is a finite surjective scheme morphism, and `k[t]` is
identified with the integral closure in the common fraction field. Its lift
to these explicit affine normalizations is an isomorphism, with empty actual
reduced-fiber branch locus. No branch or normalization assertion is assumed.

Remaining source bridges: identify the manuscript's displayed quotient
`k[x,y]/(y²-x³)` with this subalgebra; compare these explicit affine
normalizations with the project's canonical generic-stalk normalization;
and identify the ambient plane map's branch and the strict intersection.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperCuspGeometry

open CategoryTheory AlgebraicGeometry Polynomial

universe u
variable (k : Type u) [Field k]

abbrev CuspRing := Cusp.cuspAlg k
abbrev ParameterRing := Polynomial k
abbrev FunctionField := FractionRing (Polynomial k)
abbrev AffineNormalizationRing := integralClosure (CuspRing k) (FunctionField k)

abbrev cusp : Scheme := Spec (.of (CuspRing k))
abbrev parameterLine : Scheme := Spec (.of (ParameterRing k))
abbrev affineNormalization : Scheme := Spec (.of (AffineNormalizationRing k))

abbrev plane : Scheme := Spec (.of (MvPolynomial (Fin 2) k))

/-- The two coordinate functions of the cusp parametrization. -/
def planeParamPullback : MvPolynomial (Fin 2) k →ₐ[k] ParameterRing k :=
  MvPolynomial.aeval ![(X : Polynomial k) ^ 2, X ^ 3]

theorem planeParamPullback_range : (planeParamPullback k).range = CuspRing k := by
  rw [planeParamPullback, ← Algebra.adjoin_range_eq_range_aeval]
  change Algebra.adjoin k (Set.range ![(X : Polynomial k) ^ 2, X ^ 3]) = _
  congr 1
  ext p
  simp [or_comm]

/-- The surjection onto the actual cusp subalgebra. -/
def cuspCoordinateMap : MvPolynomial (Fin 2) k →ₐ[k] CuspRing k :=
  (planeParamPullback k).codRestrict (CuspRing k) (fun p => by
    rw [← planeParamPullback_range]
    exact (planeParamPullback k).mem_range_self p)

theorem cuspCoordinateMap_surjective : Function.Surjective (cuspCoordinateMap k) := by
  intro q
  have hq : q.1 ∈ (planeParamPullback k).range := by
    rw [planeParamPullback_range]
    exact q.2
  obtain ⟨p, hp⟩ := hq
  exact ⟨p, Subtype.ext hp⟩

/-- The monomial cusp is an actual closed subscheme of the plane. -/
def cuspImmersion : cusp k ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (cuspCoordinateMap k).toRingHom)

instance cuspImmersion_isClosedImmersion : IsClosedImmersion (cuspImmersion k) :=
  IsClosedImmersion.spec_of_surjective _ (cuspCoordinateMap_surjective k)

/-- The displayed cusp equation vanishes in the actual coordinate algebra. -/
theorem cusp_equation :
    cuspCoordinateMap k (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3) = 0 := by
  apply Subtype.ext
  change planeParamPullback k _ = 0
  simp [planeParamPullback]
  ring

/-- The actual parametrization `Spec k[t] → Spec k[t²,t³]`. -/
def parametrization : parameterLine k ⟶ cusp k :=
  Spec.map (CommRingCat.ofHom (algebraMap (CuspRing k) (ParameterRing k)))

instance parametrization_finite : IsFinite (parametrization k) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance parametrization_surjective : Surjective (parametrization k) := by
  constructor
  exact (RingHom.finite_algebraMap.mpr (Cusp.moduleFinite_cuspAlg k)).to_isIntegral.comap_surjective
    (show Function.Injective (algebraMap (CuspRing k) (ParameterRing k)) from Subtype.val_injective)

/-- The normalization parametrization has the whole actual closed cusp as its image. -/
theorem parametrization_image : Set.range (parametrization k) = Set.univ :=
  Set.range_eq_univ.mpr (parametrization k).surjective

/-- Its composition with the closed immersion is the displayed polynomial map. -/
theorem parametrization_immersion :
    parametrization k ≫ cuspImmersion k =
      Spec.map (CommRingCat.ofHom (planeParamPullback k).toRingHom) := by
  simp only [parametrization, cuspImmersion, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The displayed ambient polynomial endomorphism `(u,v) ↦ (u²,u³+v)`. -/
def ambientMap : plane k ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Cusp.cuspSource k)).toRingHom)

/-- The actual source-line parametrization `t ↦ (t,0)`. -/
def sourceLine : parameterLine k ⟶ plane k :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval ![(X : Polynomial k), 0]).toRingHom)

/-- Restricting the displayed ambient map to the source line gives the cusp parametrization. -/
theorem ambient_restriction_square :
    sourceLine k ≫ ambientMap k = parametrization k ≫ cuspImmersion k := by
  rw [parametrization_immersion]
  simp only [sourceLine, ambientMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  change ((MvPolynomial.aeval ![(X : Polynomial k), 0]).comp
    (MvPolynomial.aeval (Cusp.cuspSource k))).toRingHom = _
  apply congrArg (fun h : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k => h.toRingHom)
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [planeParamPullback, Cusp.cuspSource]

instance cusp_isIntegral : IsIntegral (cusp k) := inferInstance
instance parameterLine_isIntegral : IsIntegral (parameterLine k) := inferInstance

/-- The parameter ring is integrally closed; no smoothness assertion is substituted for it. -/
theorem parameterRing_integrallyClosed : IsIntegrallyClosed (ParameterRing k) := inferInstance

/-- The common function field is a fraction field of the cusp coordinate ring. -/
theorem cusp_fractionField : IsFractionRing (CuspRing k) (FunctionField k) := inferInstance

/-- The explicit integral-closure ring is the actual parameter ring over the cusp ring. -/
def affineNormalizationEquiv : AffineNormalizationRing k ≃ₐ[CuspRing k] ParameterRing k := by
  letI := Cusp.isIntegralClosure_cuspAlg k
  exact IsIntegralClosure.equiv (CuspRing k) (AffineNormalizationRing k)
    (FunctionField k) (ParameterRing k)

/-- The affine normalization projection, constructed from the integral-closure algebra. -/
def affineNormalizationProjection : affineNormalization k ⟶ cusp k :=
  Spec.map (CommRingCat.ofHom (algebraMap (CuspRing k) (AffineNormalizationRing k)))

/-- The actual lift of the parametrization to the explicit affine normalization. -/
def normalizationLift : parameterLine k ⟶ affineNormalization k :=
  Spec.map (CommRingCat.ofHom (affineNormalizationEquiv k).toRingHom)

instance normalizationLift_isIso : IsIso (normalizationLift k) := by
  let e : CommRingCat.of (AffineNormalizationRing k) ≅ CommRingCat.of (ParameterRing k) :=
    RingEquiv.toCommRingCatIso (affineNormalizationEquiv k).toRingEquiv
  change IsIso (Scheme.Spec.map e.hom.op)
  infer_instance

def normalizationIso : parameterLine k ≅ affineNormalization k := asIso (normalizationLift k)

/-- The explicit normalization lift commutes with the actual parametrization. -/
theorem normalization_square :
    normalizationLift k ≫ affineNormalizationProjection k = parametrization k := by
  simp only [normalizationLift, affineNormalizationProjection, parametrization,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro r
  exact (affineNormalizationEquiv k).commutes r

/-- Every actual scheme fiber of the normalized lift is reduced. -/
theorem normalizationLift_fiber_isReduced (y : affineNormalization k) :
    IsReduced ((normalizationLift k).fiber y) := by
  let : IsIso ((normalizationLift k).fiberToSpecResidueField y) :=
    (IsPullback.of_hasPullback (normalizationLift k)
      ((affineNormalization k).fromSpecResidueField y)).isIso_snd_of_isIso
  exact isReduced_of_isOpenImmersion ((normalizationLift k).fiberToSpecResidueField y)

/-- The normalized lift has empty actual codimension-one reduced-fiber branch set. -/
theorem normalizationLift_branch_empty : schemeReducedFiberBranch (normalizationLift k) = ∅ := by
  ext D
  simp only [schemeReducedFiberBranch, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact normalizationLift_fiber_isReduced k D.1

/-- The branch support pushed down from this explicit affine normalization is empty. -/
theorem affine_normalized_branch_support_empty :
    (affineNormalizationProjection k) ''
      (⋃ D ∈ schemeReducedFiberBranch (normalizationLift k),
        closure ({D.1} : Set (affineNormalization k))) =
      ∅ := by
  simp [normalizationLift_branch_empty]

end Pcf.Examples.CharZeroPaperCuspGeometry

#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.planeParamPullback_range
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.cuspCoordinateMap_surjective
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.cuspImmersion_isClosedImmersion
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.cusp_equation
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.parametrization_finite
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.parametrization_surjective
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.parametrization_image
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.parametrization_immersion
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.ambient_restriction_square
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.cusp_isIntegral
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.parameterLine_isIntegral
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.parameterRing_integrallyClosed
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.cusp_fractionField
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.affineNormalizationEquiv
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.normalizationLift_isIso
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.normalization_square
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.normalizationLift_fiber_isReduced
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.normalizationLift_branch_empty
#print axioms Pcf.Examples.CharZeroPaperCuspGeometry.affine_normalized_branch_support_empty
