/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationBaseChange
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientStandard

/-!
# Refining quotient-etale neighbourhoods by lifted neighbourhoods

This file proves the object-existence half of finality for quotient base change on pointed etale
neighbourhoods.  At the chosen geometric point, an etale algebra becomes standard etale after one
point-preserving localization (`Algebra.IsEtaleAt.exists_isStandardEtale`, Stacks Tag `00UE`).
The explicit lift from `StrictHenselizationQuotientStandard` then realizes that localization as a
base change from the original ring.

The map-lifting/equalization half of finality is separate; this file does not claim that quotient
base change is final or that the full comparison in Tag `05WS` is an equivalence.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Every pointed etale neighbourhood over a quotient admits a pointed map to the base change of
some pointed etale neighbourhood over the original ring. -/
theorem exists_quotientBaseChange_refinement (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    let _ : IsScalarTower R (R ⧸ I) Ω :=
      IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
    ∀ X : PointedEtaleNeighborhood (R ⧸ I) Ω,
      ∃ Y : PointedEtaleNeighborhood R Ω,
        Nonempty (X ⟶ (quotientBaseChange I φ).obj Y) := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  change ∀ X : PointedEtaleNeighborhood (R ⧸ I) Ω,
    ∃ Y : PointedEtaleNeighborhood R Ω,
      Nonempty (X ⟶ (quotientBaseChange I φ).obj Y)
  intro X
  let Q := RingHom.ker X.point.toRingHom
  let _ : Q.IsPrime := RingHom.ker_isPrime X.point.toRingHom
  let _ : Algebra.IsEtaleAt (R ⧸ I) Q := inferInstance
  obtain ⟨f, hfQ, hfstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := R ⧸ I) (S := X) Q
  let L := Localization.Away f
  let _ : Algebra.IsStandardEtale (R ⧸ I) L := hfstd
  let pointL : L →ₐ[R ⧸ I] Ω := IsLocalization.Away.liftAlgHom f
    (f := X.point) (isUnit_iff_ne_zero.mpr fun h ↦ hfQ (RingHom.mem_ker.mpr h))
  let toL : X →ₐ[R ⧸ I] L := IsScalarTower.toAlgHom (R ⧸ I) X L
  have hpointL : pointL.comp toL = X.point := by
    ext x
    simp [pointL, toL]
  let P : StandardEtalePresentation (R ⧸ I) L :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let U : StandardEtalePair R := QuotientStandardEtale.liftPair I P.P
  let e : TensorProduct R (R ⧸ I) U.Ring ≃ₐ[R ⧸ I] L :=
    (QuotientStandardEtale.tensorBaseChangeEquiv I P.P).trans P.equivRing.symm
  let tensorPoint : TensorProduct R (R ⧸ I) U.Ring →ₐ[R ⧸ I] Ω :=
    pointL.comp e.toAlgHom
  let pointU : U.Ring →ₐ[R] Ω :=
    (tensorPoint.restrictScalars R).comp Algebra.TensorProduct.includeRight
  let Y : PointedEtaleNeighborhood R Ω := ofEtaleAlgebra U.Ring pointU
  let EY : Y ≃ₐ[R] U.Ring := ofEtaleAlgebraEquiv U.Ring pointU
  let raw : X →ₐ[R ⧸ I] TensorProduct R (R ⧸ I) Y :=
    (Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I)) EY.symm.toAlgHom).comp
      (e.symm.toAlgHom.comp toL)
  let targetPoint := baseChangePoint (R := R) (S := R ⧸ I) Y
  have hraw : targetPoint.comp raw = X.point := by
    rw [← hpointL]
    apply AlgHom.ext
    intro x
    change targetPoint (raw x) = pointL (toL x)
    have htensor : targetPoint.comp
        (Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I)) EY.symm.toAlgHom) =
        tensorPoint := by
      ext
      have hEY := DFunLike.congr_fun
        (ofEtaleAlgebra_point_comp_equiv (R := R) (Ω := Ω) U.Ring pointU) U.X
      change Y.point (EY.symm U.X) = tensorPoint (1 ⊗ₜ[R] U.X) at hEY
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      simp only [targetPoint, baseChangePoint, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      exact hEY
    rw [show targetPoint (raw x) = tensorPoint (e.symm (toL x)) by
      exact DFunLike.congr_fun htensor (e.symm (toL x))]
    simp [tensorPoint]
  refine ⟨Y, ⟨?_⟩⟩
  exact homToOfEtaleAlgebra
    (TensorProduct R (R ⧸ I) Y) targetPoint raw hraw

end Pcf.Stacks.PointedEtaleNeighborhood
