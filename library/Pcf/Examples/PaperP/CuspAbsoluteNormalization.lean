/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CuspNormalization
public import Pcf.Bounding.GlobalNormalizationNormal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Pcf.Stacks.Purity.GenericBaseNormalization
public import Pcf.Stacks.Purity.Tag0BMBScheme

/-!
# The canonical normalization of the actual cusp scheme

For `paper-p.tex`, Example `ex:cusp`, these declarations compare the
explicit normalization of the quotient-coordinate scheme with Palomar's
absolute normalization.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CuspOriginalFibre

open AlgebraicGeometry CategoryTheory Polynomial

set_option linter.style.haveILetI false

variable (k : Type*) [Field k] [CharZero k]

/-- The actual cuspidal coordinate ring is a domain. -/
instance coordinateRing_isDomain : IsDomain (CoordinateRing k) :=
  Function.Injective.isDomain (Pcf.Examples.Cusp.cuspParam k).toRingHom
    (cuspParam_injective k)

/-- The actual cuspidal cubic is an integral scheme. -/
instance cuspScheme_isIntegral : IsIntegral (Spec (.of (CoordinateRing k))) :=
  inferInstance

/-- The parameter line is integral. -/
instance cuspParameterLine_isIntegral : IsIntegral (Spec (.of k[X])) := by
  infer_instance

/-- The parameter coordinate ring is integrally closed. -/
instance cuspParameterRing_isIntegrallyClosed : IsIntegrallyClosed k[X] := by
  infer_instance

omit [CharZero k] in
/-- The absolute normalization map of the already normal parameter line is
an isomorphism. -/
theorem cuspParameterNormalizationMap_isIso :
    IsIso (Pcf.Palomar.normalizationMap (Spec (.of k[X]))) := by
  exact Pcf.Stacks.genericPoint_fromNormalization_isIso (.of k[X])

/-- The absolute normalization of the actual affine cusp is affine. -/
instance cuspAbsoluteNormalization_isAffine :
    IsAffine (Pcf.Palomar.normalization (Spec (.of (CoordinateRing k)))) := by
  exact isAffine_of_isAffineHom
    (Pcf.Palomar.normalizationMap (Spec (.of (CoordinateRing k))))

/-- Global functions on the actual cusp affine scheme are its quotient
coordinate ring. -/
noncomputable def cuspGlobalSectionsEquiv :
    Γ(Spec (.of (CoordinateRing k)), ⊤) ≃+* CoordinateRing k :=
  (Scheme.ΓSpecIso (.of (CoordinateRing k))).commRingCatIsoToRingEquiv

instance cuspTop_nonempty :
    Nonempty (⊤ : (Spec (.of (CoordinateRing k))).Opens) :=
  ⟨⟨genericPoint (Spec (.of (CoordinateRing k))), trivial⟩⟩

/-- The sections on the generic preimage of the cusp are its function field. -/
noncomputable def cuspGenericSectionsEquiv :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) ≃+* X.functionField := by
  let X := Spec (.of (CoordinateRing k))
  exact (Pcf.schemeGenericInclusionSectionsIso X ⊤).commRingCatIsoToRingEquiv

/-- The generic-section comparison is compatible with the base algebra. -/
noncomputable def genericSectionsAlgEquiv (X : Scheme) [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    let f := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U) :=
      (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) X.functionField :=
      (X.germToFunctionField U).hom.toAlgebra
    Γ(Spec X.functionField, f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField := by
  let f := Pcf.schemeGenericInclusion X
  letI : Algebra Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U) :=
    (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) X.functionField :=
    (X.germToFunctionField U).hom.toAlgebra
  have hgeneric : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using
      (inferInstance : Nonempty U))
  have htop : f ⁻¹ᵁ U = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem f (by simpa [f, Pcf.schemeGenericInclusion])
  let e : Γ(Spec X.functionField, f ⁻¹ᵁ U) ≅ X.functionField :=
    (Spec X.functionField).presheaf.mapIso (eqToIso htop.symm).op ≪≫
      Scheme.ΓSpecIso X.functionField
  have he : f.app U ≫ e.hom = X.germToFunctionField U := by
    dsimp [f, Pcf.schemeGenericInclusion, e]
    rw [Scheme.fromSpecStalk_app hgeneric]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp
  exact { e.commRingCatIsoToRingEquiv with
    commutes' r := congr($(he) r) }

/-- The cusp generic-section comparison respects functions on the cusp. -/
noncomputable def cuspGenericSectionsAlgEquiv :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
      (f.app ⊤).hom.toAlgebra
    letI : Algebra Γ(X, ⊤) X.functionField :=
      (X.germToFunctionField ⊤).hom.toAlgebra
    Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) ≃ₐ[Γ(X, ⊤)] X.functionField := by
  exact genericSectionsAlgEquiv (Spec (.of (CoordinateRing k))) ⊤

/-- The cusp's actual function field is a fraction ring of its quotient
coordinate ring via the affine global-sections identification. -/
theorem cuspFunctionField_isFractionRing :
    let X := Spec (.of (CoordinateRing k))
    letI : Algebra (CoordinateRing k) X.functionField :=
      ((X.germToFunctionField ⊤).hom.comp
        (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
    IsFractionRing (CoordinateRing k) X.functionField := by
  let X := Spec (.of (CoordinateRing k))
  letI : Algebra Γ(X, ⊤) X.functionField :=
    (X.germToFunctionField ⊤).hom.toAlgebra
  letI : Algebra (CoordinateRing k) X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  apply IsFractionRing.of_ringEquiv_left
    (cuspGlobalSectionsEquiv k).symm
  intro c
  rfl

/-- The actual function field is canonically the parameter fraction field,
as an algebra over the actual cusp coordinate ring. -/
noncomputable def cuspFunctionFieldEquiv :
    let X := Spec (.of (CoordinateRing k))
    letI : Algebra (CoordinateRing k) X.functionField :=
      ((X.germToFunctionField ⊤).hom.comp
        (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    X.functionField ≃ₐ[CoordinateRing k] FractionRing k[X] := by
  let X := Spec (.of (CoordinateRing k))
  letI : Algebra (CoordinateRing k) X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : IsFractionRing (CoordinateRing k) X.functionField :=
    cuspFunctionField_isFractionRing k
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : IsFractionRing (CoordinateRing k) (FractionRing k[X]) :=
    coordinateRing_isFractionRing_canonical k
  exact ((FractionRing.algEquiv (A := CoordinateRing k) X.functionField).symm.trans
    (FractionRing.algEquiv (A := CoordinateRing k) (FractionRing k[X])))

/-- The generic preimage's coordinate ring is the parameter fraction field. -/
noncomputable def cuspGenericSectionsParameterEquiv :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) ≃+* FractionRing k[X] := by
  let X := Spec (.of (CoordinateRing k))
  let f := Pcf.schemeGenericInclusion X
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
    (f.app ⊤).hom.toAlgebra
  letI : Algebra Γ(X, ⊤) X.functionField :=
    (X.germToFunctionField ⊤).hom.toAlgebra
  letI : Algebra (CoordinateRing k) X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  exact (cuspGenericSectionsAlgEquiv k).toRingEquiv.trans
    (cuspFunctionFieldEquiv k).toRingEquiv

/-- The generic section identification commutes with the maps from cusp
global sections and from the quotient coordinate ring. -/
theorem cuspGenericSectionsParameterEquiv_commutes (r :
    Γ(Spec (.of (CoordinateRing k)), ⊤)) :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
      (f.app ⊤).hom.toAlgebra
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    cuspGenericSectionsParameterEquiv k
      (algebraMap Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) r) =
      algebraMap (CoordinateRing k) (FractionRing k[X]) (cuspGlobalSectionsEquiv k r) := by
  let X := Spec (.of (CoordinateRing k))
  let f := Pcf.schemeGenericInclusion X
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
    (f.app ⊤).hom.toAlgebra
  letI : Algebra (CoordinateRing k) X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  dsimp only [cuspGenericSectionsParameterEquiv, RingEquiv.trans_apply]
  change cuspFunctionFieldEquiv k
    (cuspGenericSectionsAlgEquiv k (algebraMap Γ(X, ⊤)
      Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) r)) = _
  rw [(cuspGenericSectionsAlgEquiv k).commutes r]
  letI : Algebra Γ(X, ⊤) X.functionField :=
    (X.germToFunctionField ⊤).hom.toAlgebra
  have hr : algebraMap Γ(X, ⊤) X.functionField r =
      algebraMap (CoordinateRing k) X.functionField
        (cuspGlobalSectionsEquiv k r) := by
    change (X.germToFunctionField ⊤).hom r =
      (X.germToFunctionField ⊤).hom
        ((Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom
          ((Scheme.ΓSpecIso (.of (CoordinateRing k))).hom.hom r))
    simp
  rw [hr]
  exact (cuspFunctionFieldEquiv k).commutes _

/-- Integrality over actual cusp global sections is carried to integrality
over the quotient coordinate ring in the parameter fraction field. -/
theorem cuspGenericSections_isIntegral_iff (z :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    Γ(Spec X.functionField, f ⁻¹ᵁ ⊤)) :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
      (f.app ⊤).hom.toAlgebra
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    IsIntegral Γ(X, ⊤) z ↔
      IsIntegral (CoordinateRing k) (cuspGenericSectionsParameterEquiv k z) := by
  let X := Spec (.of (CoordinateRing k))
  let f := Pcf.schemeGenericInclusion X
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
    (f.app ⊤).hom.toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  let e := cuspGlobalSectionsEquiv k
  let g := cuspGenericSectionsParameterEquiv k
  have hsq : (algebraMap (CoordinateRing k) (FractionRing k[X])).comp e.toRingHom =
      g.toRingHom.comp (algebraMap Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤)) := by
    ext r
    exact (cuspGenericSectionsParameterEquiv_commutes k r).symm
  have hsq' : (algebraMap Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤)).comp
      e.symm.toRingHom =
      g.symm.toRingHom.comp (algebraMap (CoordinateRing k) (FractionRing k[X])) := by
    apply RingHom.ext
    intro a
    apply g.injective
    change g (algebraMap Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤)
      (e.symm a)) = g (g.symm (algebraMap (CoordinateRing k) (FractionRing k[X]) a))
    rw [cuspGenericSectionsParameterEquiv_commutes, e.apply_symm_apply,
      g.apply_symm_apply]
  constructor
  · intro hz
    exact hz.map_of_comp_eq e.toRingHom g.toRingHom hsq
  · intro hz
    have hz' := hz.map_of_comp_eq e.symm.toRingHom g.symm.toRingHom hsq'
    change IsIntegral Γ(X, ⊤) (g.symm (g z)) at hz'
    rwa [g.symm_apply_apply] at hz'

/-- The integral closure ring in Palomar's affine normalization chart is
the integral closure ring in the explicit parameter fraction field. -/
noncomputable def cuspIntegralClosureEquiv :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
      (f.app ⊤).hom.toAlgebra
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    integralClosure Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) ≃+*
      integralClosure (CoordinateRing k) (FractionRing k[X]) := by
  let X := Spec (.of (CoordinateRing k))
  let f := Pcf.schemeGenericInclusion X
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
    (f.app ⊤).hom.toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  let g := cuspGenericSectionsParameterEquiv k
  refine {
    toFun := fun z => ⟨g z.1, (cuspGenericSections_isIntegral_iff k z.1).mp z.2⟩
    invFun := fun z => ⟨g.symm z.1, (cuspGenericSections_isIntegral_iff k
      (g.symm z.1)).mpr (by
        rw [g.apply_symm_apply]
        exact z.property)⟩
    left_inv := fun z => Subtype.ext (g.symm_apply_apply z.1)
    right_inv := fun z => Subtype.ext (g.apply_symm_apply z.1)
    map_mul' := fun x y => Subtype.ext (g.map_mul x.1 y.1)
    map_add' := fun x y => Subtype.ext (g.map_add x.1 y.1) }

/-- The integral-closure equivalence respects the cusp coordinate maps. -/
theorem cuspIntegralClosureEquiv_commutes (r :
    Γ(Spec (.of (CoordinateRing k)), ⊤)) :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
      (f.app ⊤).hom.toAlgebra
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    cuspIntegralClosureEquiv k
      (algebraMap Γ(X, ⊤)
        (integralClosure Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤)) r) =
      algebraMap (CoordinateRing k)
        (integralClosure (CoordinateRing k) (FractionRing k[X]))
          (cuspGlobalSectionsEquiv k r) := by
  let X := Spec (.of (CoordinateRing k))
  let f := Pcf.schemeGenericInclusion X
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
    (f.app ⊤).hom.toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  apply Subtype.ext
  change cuspGenericSectionsParameterEquiv k
    (algebraMap Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) r) = _
  exact cuspGenericSectionsParameterEquiv_commutes k r

/-- The inverse integral-closure equivalence also preserves the explicit
coordinate map from the quotient ring. -/
theorem cuspIntegralClosureEquiv_symm_commutes (a : CoordinateRing k) :
    let X := Spec (.of (CoordinateRing k))
    let f := Pcf.schemeGenericInclusion X
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
      (f.app ⊤).hom.toAlgebra
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    (cuspIntegralClosureEquiv k).symm
      (algebraMap (CoordinateRing k)
        (integralClosure (CoordinateRing k) (FractionRing k[X])) a) =
      algebraMap Γ(X, ⊤)
        (integralClosure Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤))
          ((cuspGlobalSectionsEquiv k).symm a) := by
  let X := Spec (.of (CoordinateRing k))
  let f := Pcf.schemeGenericInclusion X
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, f ⁻¹ᵁ ⊤) :=
    (f.app ⊤).hom.toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  apply (cuspIntegralClosureEquiv k).injective
  rw [(cuspIntegralClosureEquiv k).apply_symm_apply,
    cuspIntegralClosureEquiv_commutes,
    (cuspGlobalSectionsEquiv k).apply_symm_apply]

/-- The canonical absolute normalization is the spectrum of the integral
closure in its actual function field, on the whole affine cusp. -/
noncomputable def cuspAbsoluteNormalizationIntegralClosureIso :
    let X := Spec (.of (CoordinateRing k))
    let f := X.fromSpecStalk (genericPoint X)
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, ⊤) :=
      (f.app ⊤).hom.toAlgebra
    Pcf.Palomar.normalization X ≅
      Spec (.of (integralClosure Γ(X, ⊤) Γ(Spec X.functionField, ⊤))) := by
  let X := Spec (.of (CoordinateRing k))
  let f := X.fromSpecStalk (genericPoint X)
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, ⊤) :=
    (f.app ⊤).hom.toAlgebra
  let e := f.normalizationObjIso (isAffineOpen_top X)
  exact (Pcf.Palomar.normalization X).isoSpec ≪≫ (Scheme.Spec.mapIso e.op).symm

/-- The canonical absolute normalization of the actual cuspidal cubic is
the affine parameter line `Spec k[u]`. -/
noncomputable def cuspAbsoluteNormalizationSpecIso :
    Pcf.Palomar.normalization (Spec (.of (CoordinateRing k))) ≅
      Spec (.of k[X]) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  let e := cuspIntegralClosureEquiv k
  exact (cuspAbsoluteNormalizationIntegralClosureIso k) ≪≫
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm ≪≫
      (coordinateRing_integralClosureSpecIso k).symm

/-- The canonical identification with the parameter line is étale. -/
theorem cuspAbsoluteNormalizationSpecIso_isEtale :
    Etale (cuspAbsoluteNormalizationSpecIso k).hom := by
  infer_instance


/-- Every point of the canonical identification with the parameter line is
étale in the pointwise Stacks sense. -/
theorem cuspAbsoluteNormalizationSpecIso_isStacksEtaleAt
    (x : Pcf.Palomar.normalization (Spec (.of (CoordinateRing k)))) :
    Pcf.Stacks.IsStacksEtaleAt (cuspAbsoluteNormalizationSpecIso k).hom x := by
  letI : Etale (cuspAbsoluteNormalizationSpecIso k).hom :=
    cuspAbsoluteNormalizationSpecIso_isEtale k
  refine ⟨⊤, isAffineOpen_top (Pcf.Palomar.normalization
    (Spec (.of (CoordinateRing k)))), ⊤,
    isAffineOpen_top (Spec (.of k[X])), ?_, ?_, ?_⟩
  · simp
  · trivial
  · exact Etale.etale_appLE (cuspAbsoluteNormalizationSpecIso k).hom
      (isAffineOpen_top (Spec (.of k[X])))
      (isAffineOpen_top (Pcf.Palomar.normalization
        (Spec (.of (CoordinateRing k))))) (by simp)

/-- The pointwise non-étale locus of the canonical identification with the
parameter line is empty. -/
theorem cuspAbsoluteNormalizationSpecIso_nonEtaleLocus_empty :
    {x : Pcf.Palomar.normalization (Spec (.of (CoordinateRing k))) |
      ¬ Pcf.Stacks.IsStacksEtaleAt (cuspAbsoluteNormalizationSpecIso k).hom x} = ∅ := by
  ext x
  simp [cuspAbsoluteNormalizationSpecIso_isStacksEtaleAt]

/-- The affine normalization map on global functions is the integral-closure
inclusion followed by the normalization chart's inverse. -/
theorem cuspNormalizationMap_appTop :
    let X := Spec (.of (CoordinateRing k))
    let f := X.fromSpecStalk (genericPoint X)
    letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, ⊤) :=
      (f.app ⊤).hom.toAlgebra
    (Pcf.Palomar.normalizationMap X).appTop =
      CommRingCat.ofHom (algebraMap Γ(X, ⊤)
        (integralClosure Γ(X, ⊤) Γ(Spec X.functionField, ⊤))) ≫
        (f.normalizationObjIso (isAffineOpen_top X)).inv := by
  let X := Spec (.of (CoordinateRing k))
  let f := X.fromSpecStalk (genericPoint X)
  letI : Algebra Γ(X, ⊤) Γ(Spec X.functionField, ⊤) :=
    (f.app ⊤).hom.toAlgebra
  exact f.fromNormalization_app (isAffineOpen_top X)

/-- The generic point of the cusp maps into the parameter line through the
canonical identification of function fields. -/
noncomputable def cuspGenericToParameterLine :
    let X := Spec (.of (CoordinateRing k))
    Spec X.functionField ⟶ Spec (.of k[X]) := by
  let X := Spec (.of (CoordinateRing k))
  letI : Algebra (CoordinateRing k) X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  exact Spec.map (CommRingCat.ofHom
    ((cuspFunctionFieldEquiv k).symm.toRingHom.comp
      (algebraMap k[X] (FractionRing k[X]))))

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic-point map of the cusp factors through its explicit
parametrization via the parameter line. -/
theorem cuspGenericToParameterLine_comp :
    cuspGenericToParameterLine k ≫ schemeMap k =
      Pcf.schemeGenericInclusion (Spec (.of (CoordinateRing k))) := by
  let X := Spec (.of (CoordinateRing k))
  letI : Algebra (CoordinateRing k) X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  unfold cuspGenericToParameterLine schemeMap Pcf.schemeGenericInclusion
  rw [Spec.fromSpecStalk_eq, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (cuspFunctionFieldEquiv k).symm
    (algebraMap k[X] (FractionRing k[X])
      ((Pcf.Examples.Cusp.cuspParam k).toRingHom a)) =
    algebraMap (CoordinateRing k) X.functionField a
  exact (cuspFunctionFieldEquiv k).symm.commutes a

/-- The canonical map from the absolute cusp normalization to the explicit
parameter line, obtained from the factorization of its generic point. -/
noncomputable def cuspNormalizationToParameterLine :
    Pcf.Palomar.normalization (Spec (.of (CoordinateRing k))) ⟶
      Spec (.of k[X]) := by
  letI : IsFinite (schemeMap k) := schemeMap_isFinite k
  exact (Pcf.schemeGenericInclusion (Spec (.of (CoordinateRing k)))).normalizationDesc
    (cuspGenericToParameterLine k) (schemeMap k)
      (cuspGenericToParameterLine_comp k).symm

/-- This canonical comparison is over the actual cusp scheme. -/
theorem cuspNormalizationToParameterLine_comp :
    cuspNormalizationToParameterLine k ≫ schemeMap k =
      Pcf.Palomar.normalizationMap (Spec (.of (CoordinateRing k))) := by
  letI : IsFinite (schemeMap k) := schemeMap_isFinite k
  unfold cuspNormalizationToParameterLine
  exact (Pcf.schemeGenericInclusion
    (Spec (.of (CoordinateRing k)))).normalizationDesc_comp
      (cuspGenericToParameterLine k) (schemeMap k)
      (cuspGenericToParameterLine_comp k).symm

/-- The actual cusp function field is also the fraction field of the
parameter polynomial ring through the generic-to-parameter map. -/
theorem cuspParameterLine_generic_isFractionRing :
    let K := (Spec (.of (CoordinateRing k))).functionField
    letI : Algebra (CoordinateRing k) K :=
      (((Spec (.of (CoordinateRing k))).germToFunctionField ⊤).hom.comp
        (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    letI : Algebra k[X] K :=
      ((cuspFunctionFieldEquiv k).symm.toRingEquiv.toRingHom.comp
        (algebraMap k[X] (FractionRing k[X]))).toAlgebra
    IsFractionRing k[X] K := by
  let K := (Spec (.of (CoordinateRing k))).functionField
  letI : Algebra (CoordinateRing k) K :=
    (((Spec (.of (CoordinateRing k))).germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : Algebra k[X] K :=
    ((cuspFunctionFieldEquiv k).symm.toRingEquiv.toRingHom.comp
      (algebraMap k[X] (FractionRing k[X]))).toAlgebra
  let e : FractionRing k[X] ≃ₐ[k[X]] K :=
    { (cuspFunctionFieldEquiv k).symm.toRingEquiv with
      commutes' a := rfl }
  exact IsFractionRing.of_algEquiv e

/-- The coordinate ring of the parameter line is integrally closed in the
sections over the actual cusp's generic function field. -/
theorem cuspParameterLine_generic_isIntegrallyClosedIn :
    let K := (Spec (.of (CoordinateRing k))).functionField
    let f := cuspGenericToParameterLine k
    letI : Algebra Γ(Spec (.of k[X]), ⊤) Γ(Spec K, ⊤) :=
      f.appTop.hom.toAlgebra
    IsIntegrallyClosedIn Γ(Spec (.of k[X]), ⊤) Γ(Spec K, ⊤) := by
  let R := (.of k[X] : CommRingCat)
  let K := (Spec (.of (CoordinateRing k))).functionField
  let f := cuspGenericToParameterLine k
  letI : Algebra (CoordinateRing k) K :=
    (((Spec (.of (CoordinateRing k))).germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of (CoordinateRing k))).inv.hom).toAlgebra
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : Algebra R K :=
    ((cuspFunctionFieldEquiv k).symm.toRingEquiv.toRingHom.comp
      (algebraMap k[X] (FractionRing k[X]))).toAlgebra
  letI : IsFractionRing R K := cuspParameterLine_generic_isFractionRing k
  let S := Γ(Spec R, ⊤)
  let T := Γ(Spec K, ⊤)
  letI : Algebra S T := f.appTop.hom.toAlgebra
  let φ : R ≃+* S := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let ψ : T ≃+* K := (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv
  letI : Algebra R T := Algebra.compHom T φ.toRingHom
  have hcomp : (algebraMap S T).comp φ.toRingHom = algebraMap R T := rfl
  let j : R ⟶ K := CommRingCat.ofHom (algebraMap R K)
  have hf : f = Spec.map j := by
    dsimp [f, j, cuspGenericToParameterLine]
    rfl
  have hn := Scheme.ΓSpecIso_inv_naturality j
  rw [← hf] at hn
  have hnat (r : R) : ψ ((algebraMap R T) r) = algebraMap R K r := by
    have h := congrArg (fun (z : R ⟶ T) => z.hom r) hn
    change (Scheme.ΓSpecIso K).inv.hom (algebraMap R K r) =
      f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) at h
    change ψ (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) = _
    rw [← h]
    change ψ (ψ.symm (algebraMap R K r)) = _
    exact ψ.apply_symm_apply _
  have hnat' : ψ.toRingHom.comp (algebraMap R T) = algebraMap R K := by
    apply RingHom.ext
    intro r
    exact hnat r
  have hmapinj : Function.Injective (algebraMap R T) := by
    intro a b hab
    apply (IsFractionRing.injective R K)
    rw [← hnat a, ← hnat b, hab]
  have hinj : Function.Injective (algebraMap S T) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := φ.surjective a
    obtain ⟨b, rfl⟩ := φ.surjective b
    change ((algebraMap S T).comp φ.toRingHom) a =
      ((algebraMap S T).comp φ.toRingHom) b at hab
    rw [hcomp] at hab
    exact congrArg φ (hmapinj hab)
  apply (isIntegrallyClosedIn_iff).mpr
  refine ⟨hinj, ?_⟩
  intro x hx
  have hR : IsIntegral R x := (φ.isIntegral_iff hcomp x).mpr hx
  have hRK : IsIntegral R (ψ x) :=
    IsIntegral.map_of_comp_eq (RingHom.id R) ψ.toRingHom (by simpa using hnat'.symm) hR
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp inferInstance hRK
  refine ⟨φ y, ?_⟩
  apply ψ.injective
  change ψ (((algebraMap S T).comp φ.toRingHom) y) = ψ x
  rw [hcomp, hnat y]
  exact hy

/-- Normalizing the parameter line in the actual cusp function field gives
the parameter line itself. -/
theorem cuspGenericToParameterLine_fromNormalization_isIso :
    IsIso (cuspGenericToParameterLine k).fromNormalization := by
  let R := (.of k[X] : CommRingCat)
  let K := (Spec (.of (CoordinateRing k))).functionField
  let f := cuspGenericToParameterLine k
  let S := Γ(Spec R, ⊤)
  let T := Γ(Spec K, f ⁻¹ᵁ (⊤ : (Spec R).Opens))
  letI : Algebra S T := (f.app ⊤).hom.toAlgebra
  have hnormal : IsIntegrallyClosedIn S T := by
    convert cuspParameterLine_generic_isIntegrallyClosedIn k using 1
    rfl
  let B := integralClosure S T
  have hbij : Function.Bijective (algebraMap S B) := by
    constructor
    · intro a b h
      apply (isIntegrallyClosedIn_iff.mp hnormal).1
      exact congrArg (Subalgebra.val B) h
    · intro x
      obtain ⟨s, hs⟩ := (isIntegrallyClosedIn_iff.mp hnormal).2 x.property
      refine ⟨s, ?_⟩
      apply Subtype.ext
      exact hs
  have hTop : IsIso f.fromNormalization.appTop := by
    change IsIso (f.fromNormalization.app ⊤)
    rw [f.fromNormalization_app (isAffineOpen_top (Spec R))]
    haveI : IsIso (CommRingCat.ofHom (algebraMap S B)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    infer_instance
  letI : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have hSpec : IsIso (Spec.map f.fromNormalization.appTop) := inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine f.fromNormalization)).mpr hSpec

/-- Transitivity of relative normalization for a specified factorization. -/
private theorem normalizationDesc_isIso_of_factor
    {X Y Z : Scheme} (h : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom g]
    [QuasiCompact h] [QuasiSeparated h] [IsIso f.fromNormalization]
    (H : h = f ≫ g) : IsIso (h.normalizationDesc f g H) := by
  let d := h.normalizationDesc f g H
  let e := f.normalizationDesc h.toNormalization d (by
    rw [h.toNormalization_normalizationDesc])
  let s : Y ⟶ h.normalization := inv f.fromNormalization ≫ e
  have hsd : s ≫ d = 𝟙 Y := by
    dsimp [s]
    rw [Category.assoc, f.normalizationDesc_comp]
    simp
  have hfs : f ≫ s = h.toNormalization := by
    calc
      f ≫ s = (f.toNormalization ≫ f.fromNormalization) ≫ s := by
        exact congrArg (fun q : X ⟶ Y => q ≫ s) f.toNormalization_fromNormalization.symm
      _ = f.toNormalization ≫ e := by
        simp only [s, Category.assoc, IsIso.hom_inv_id_assoc]
      _ = h.toNormalization := f.toNormalization_normalizationDesc _ _ _
  have hsg : s ≫ h.fromNormalization = g := by
    calc
      s ≫ h.fromNormalization = s ≫ (d ≫ g) := by rw [h.normalizationDesc_comp]
      _ = (s ≫ d) ≫ g := by simp [Category.assoc]
      _ = g := by rw [hsd]; simp
  have hds : d ≫ s = 𝟙 h.normalization := by
    apply Scheme.Hom.normalization.hom_ext h (d ≫ s) (𝟙 _) h.fromNormalization
    · calc
        h.toNormalization ≫ (d ≫ s) = (h.toNormalization ≫ d) ≫ s := by
          simp [Category.assoc]
        _ = f ≫ s := by rw [h.toNormalization_normalizationDesc]
        _ = h.toNormalization := hfs
        _ = h.toNormalization ≫ 𝟙 _ := by simp
    · rw [Category.assoc, hsg, h.normalizationDesc_comp]
    · simp
  exact ⟨s, hds, hsd⟩

/-- The normalization comparison induced by the cusp parametrization is an
isomorphism. -/
theorem cuspNormalizationToParameterLine_isIso :
    IsIso (cuspNormalizationToParameterLine k) := by
  let f := cuspGenericToParameterLine k
  let g := schemeMap k
  letI : IsFinite g := schemeMap_isFinite k
  letI : IsIso f.fromNormalization :=
    cuspGenericToParameterLine_fromNormalization_isIso k
  haveI : QuasiCompact f := inferInstance
  haveI : QuasiSeparated f := inferInstance
  haveI : QuasiCompact (Pcf.schemeGenericInclusion
      (Spec (.of (CoordinateRing k)))) := inferInstance
  haveI : QuasiSeparated (Pcf.schemeGenericInclusion
      (Spec (.of (CoordinateRing k)))) := inferInstance
  exact normalizationDesc_isIso_of_factor
    (Pcf.schemeGenericInclusion (Spec (.of (CoordinateRing k)))) f g
      (cuspGenericToParameterLine_comp k).symm

/-- The normalized cusp lift obtained from the canonical over-cusp
comparison. -/
noncomputable def cuspNormalizedLift :
    Pcf.Palomar.normalization (Spec (.of k[X])) ⟶
      Pcf.Palomar.normalization (Spec (.of (CoordinateRing k))) := by
  letI : IsIso (cuspNormalizationToParameterLine k) :=
    cuspNormalizationToParameterLine_isIso k
  exact Pcf.Palomar.normalizationMap (Spec (.of k[X])) ≫
    inv (cuspNormalizationToParameterLine k)

/-- The normalized lift commutes with the actual cusp parametrization. -/
theorem cuspNormalizedLift_comp :
    cuspNormalizedLift k ≫
      Pcf.Palomar.normalizationMap (Spec (.of (CoordinateRing k))) =
    Pcf.Palomar.normalizationMap (Spec (.of k[X])) ≫ schemeMap k := by
  letI : IsIso (cuspNormalizationToParameterLine k) :=
    cuspNormalizationToParameterLine_isIso k
  unfold cuspNormalizedLift
  rw [← cuspNormalizationToParameterLine_comp k]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-- The normalized cusp lift is an isomorphism. -/
theorem cuspNormalizedLift_isIso : IsIso (cuspNormalizedLift k) := by
  letI : IsIso (Pcf.Palomar.normalizationMap (Spec (.of k[X]))) :=
    cuspParameterNormalizationMap_isIso k
  letI : IsIso (cuspNormalizationToParameterLine k) :=
    cuspNormalizationToParameterLine_isIso k
  unfold cuspNormalizedLift
  infer_instance

/-- The normalized cusp lift is étale everywhere. -/
theorem cuspNormalizedLift_isEtale : Etale (cuspNormalizedLift k) := by
  letI : IsIso (cuspNormalizedLift k) := cuspNormalizedLift_isIso k
  infer_instance

/-- The normalized lift is étale at every point in the pointwise Stacks
sense used for the branch locus. -/
theorem cuspNormalizedLift_isStacksEtaleAt
    (x : Pcf.Palomar.normalization (Spec (.of k[X]))) :
    Pcf.Stacks.IsStacksEtaleAt (cuspNormalizedLift k) x := by
  letI : Etale (cuspNormalizedLift k) := cuspNormalizedLift_isEtale k
  letI : IsAffine (Pcf.Palomar.normalization (Spec (.of k[X]))) :=
    isAffine_of_isAffineHom (Pcf.Palomar.normalizationMap (Spec (.of k[X])))
  refine ⟨⊤, isAffineOpen_top _, ⊤,
    isAffineOpen_top (Pcf.Palomar.normalization
      (Spec (.of (CoordinateRing k)))), ?_, ?_, ?_⟩
  · simp
  · trivial
  · exact Etale.etale_appLE (cuspNormalizedLift k)
      (isAffineOpen_top (Pcf.Palomar.normalization
        (Spec (.of (CoordinateRing k)))))
      (isAffineOpen_top (Pcf.Palomar.normalization (Spec (.of k[X]))))
      (by simp)

/-- The normalized cusp lift has empty pointwise non-étale locus. -/
theorem cuspNormalizedLift_nonEtaleLocus_empty :
    {x : Pcf.Palomar.normalization (Spec (.of k[X])) |
      ¬ Pcf.Stacks.IsStacksEtaleAt (cuspNormalizedLift k) x} = ∅ := by
  ext x
  simp [cuspNormalizedLift_isStacksEtaleAt]

set_option backward.isDefEq.respectTransparency.types false in
/-- The finite cusp parametrization is surjective, hence dominant. -/
theorem cuspSchemeMap_isDominant : IsDominant (schemeMap k) := by
  have hs : Function.Surjective
      (PrimeSpectrum.comap (Pcf.Examples.Cusp.cuspParam k).toRingHom) :=
    (cuspParam_finite k).to_isIntegral.comap_surjective (cuspParam_injective k)
  haveI : Surjective (schemeMap k) := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, by
      change PrimeSpectrum.comap (Pcf.Examples.Cusp.cuspParam k).toRingHom x = y
      exact hx⟩
  infer_instance

#print axioms coordinateRing_isDomain
#print axioms cuspAbsoluteNormalization_isAffine
#print axioms cuspGenericSectionsEquiv
#print axioms cuspGenericSectionsAlgEquiv
#print axioms cuspFunctionField_isFractionRing
#print axioms cuspFunctionFieldEquiv
#print axioms cuspGenericSections_isIntegral_iff
#print axioms cuspIntegralClosureEquiv_commutes
#print axioms cuspIntegralClosureEquiv_symm_commutes
#print axioms cuspAbsoluteNormalizationIntegralClosureIso
#print axioms cuspAbsoluteNormalizationSpecIso
#print axioms cuspAbsoluteNormalizationSpecIso_isEtale
#print axioms cuspAbsoluteNormalizationSpecIso_isStacksEtaleAt
#print axioms cuspAbsoluteNormalizationSpecIso_nonEtaleLocus_empty
#print axioms cuspNormalizationMap_appTop
#print axioms cuspGenericToParameterLine_comp
#print axioms cuspNormalizationToParameterLine_comp
#print axioms cuspParameterLine_generic_isFractionRing
#print axioms cuspParameterLine_generic_isIntegrallyClosedIn
#print axioms cuspGenericToParameterLine_fromNormalization_isIso
#print axioms cuspNormalizationToParameterLine_isIso
#print axioms cuspNormalizedLift_comp
#print axioms cuspNormalizedLift_isIso
#print axioms cuspNormalizedLift_nonEtaleLocus_empty
#print axioms cuspSchemeMap_isDominant
#print axioms cuspParameterNormalizationMap_isIso

end Pcf.Examples.PaperP.CuspOriginalFibre
