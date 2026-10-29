/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CuspOriginalFibre
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Normalization of the actual cuspidal cubic in `paper-p.tex`

The quotient coordinate ring of `y² = x³` is identified with its
integral closure in `k(u)`, with normalization morphism given by
`x ↦ u²`, `y ↦ u³`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CuspOriginalFibre

open AlgebraicGeometry CategoryTheory Polynomial

set_option linter.style.haveILetI false

variable (k : Type*) [Field k] [CharZero k]

/-- The cusp parameter field is the function field of the actual quotient
coordinate ring. -/
theorem coordinateRing_isFractionRing :
    letI : Algebra (CoordinateRing k) (FractionRing k[X]) :=
      ((algebraMap k[X] (FractionRing k[X])).comp
        (Pcf.Examples.Cusp.cuspParam k).toRingHom).toAlgebra
    IsFractionRing (CoordinateRing k) (FractionRing k[X]) := by
  letI : Algebra (CoordinateRing k) (FractionRing k[X]) :=
    ((algebraMap k[X] (FractionRing k[X])).comp
      (Pcf.Examples.Cusp.cuspParam k).toRingHom).toAlgebra
  letI : IsFractionRing (Pcf.Examples.Cusp.cuspAlg k) (FractionRing k[X]) :=
    Pcf.Examples.Cusp.isFractionRing_cuspAlg k
  apply IsFractionRing.of_ringEquiv_left
    (coordinateRingEquivCuspAlg k).toRingEquiv
  intro c
  rfl

/-- The same function-field identification using the canonical algebra
structure on the polynomial fraction ring. -/
theorem coordinateRing_isFractionRing_canonical :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    IsFractionRing (CoordinateRing k) (FractionRing k[X]) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : IsFractionRing (Pcf.Examples.Cusp.cuspAlg k) (FractionRing k[X]) :=
    Pcf.Examples.Cusp.isFractionRing_cuspAlg k
  apply IsFractionRing.of_ringEquiv_left
    (coordinateRingEquivCuspAlg k).toRingEquiv
  intro c
  rfl

/-- Integral closure in the localization algebra structure on `k(u)`. -/
theorem coordinateRing_isIntegralClosure_canonical :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    IsIntegralClosure k[X] (CoordinateRing k) (FractionRing k[X]) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : IsIntegralClosure k[X] (Pcf.Examples.Cusp.cuspAlg k)
      (FractionRing k[X]) := Pcf.Examples.Cusp.isIntegralClosure_cuspAlg k
  have hcompat :
      (algebraMap (Pcf.Examples.Cusp.cuspAlg k) (FractionRing k[X])).comp
        (coordinateRingEquivCuspAlg k).toRingEquiv.toRingHom =
      algebraMap (CoordinateRing k) (FractionRing k[X]) := by
    apply RingHom.ext
    intro c
    change algebraMap k[X] (FractionRing k[X])
      ((coordinateRingEquivCuspAlg k c : Pcf.Examples.Cusp.cuspAlg k) : k[X]) =
      algebraMap k[X] (FractionRing k[X]) (Pcf.Examples.Cusp.cuspParam k c)
    rfl
  refine { algebraMap_injective := IsFractionRing.injective k[X] (FractionRing k[X]),
           isIntegral_iff := ?_ }
  intro z
  exact (RingEquiv.isIntegral_iff (coordinateRingEquivCuspAlg k).toRingEquiv
    hcompat z).trans (IsIntegralClosure.isIntegral_iff
      (A := k[X]) (R := Pcf.Examples.Cusp.cuspAlg k) (B := FractionRing k[X]))

/-- The parameter ring is the integral closure of the actual cuspidal
quotient coordinate ring in its function field. -/
noncomputable def coordinateRing_integralClosureEquiv :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    k[X] ≃ₐ[CoordinateRing k]
      integralClosure (CoordinateRing k) (FractionRing k[X]) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : IsIntegralClosure k[X] (CoordinateRing k) (FractionRing k[X]) :=
    coordinateRing_isIntegralClosure_canonical k
  exact IsIntegralClosure.equiv (CoordinateRing k) k[X] (FractionRing k[X])
    (integralClosure (CoordinateRing k) (FractionRing k[X]))

/-- The actual cusp parameter line is the spectrum of the integral closure
of its quotient coordinate ring. -/
noncomputable def coordinateRing_integralClosureSpecIso :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    Spec (.of k[X]) ≅
      Spec (.of (integralClosure (CoordinateRing k) (FractionRing k[X]))) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  exact (Scheme.Spec.mapIso
    (coordinateRing_integralClosureEquiv k).toCommRingCatIso.op).symm

/-- The normalization identification respects the original cusp map. -/
theorem coordinateRing_integralClosureSpecIso_over_cusp :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    (coordinateRing_integralClosureSpecIso k).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (CoordinateRing k)
          (integralClosure (CoordinateRing k) (FractionRing k[X])))) =
      schemeMap k := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  unfold coordinateRing_integralClosureSpecIso schemeMap
  simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change (coordinateRing_integralClosureEquiv k).symm
    (algebraMap (CoordinateRing k)
      (integralClosure (CoordinateRing k) (FractionRing k[X])) c) =
    (Pcf.Examples.Cusp.cuspParam k).toRingHom c
  rw [← (coordinateRing_integralClosureEquiv k).commutes c,
    AlgEquiv.symm_apply_apply]
  rfl

/-- The original cusp parametrization is finite as a map of its actual
coordinate rings. -/
theorem cuspParam_finite :
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.Finite := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  haveI : Module.Finite (Pcf.Examples.Cusp.cuspAlg k) k[X] :=
    Pcf.Examples.Cusp.moduleFinite_cuspAlg k
  have hcompat :
      (algebraMap (CoordinateRing k) k[X]).comp
        (coordinateRingEquivCuspAlg k).symm.toRingEquiv.toRingHom =
      (RingEquiv.refl k[X]).toRingHom.comp
        (algebraMap (Pcf.Examples.Cusp.cuspAlg k) k[X]) := by
    apply RingHom.ext
    intro c
    change Pcf.Examples.Cusp.cuspParam k
      ((coordinateRingEquivCuspAlg k).symm c) = (c : k[X])
    exact Subtype.ext_iff.mp ((coordinateRingEquivCuspAlg k).apply_symm_apply c)
  haveI : Module.Finite (CoordinateRing k) k[X] :=
    Module.Finite.of_equiv_equiv
      (coordinateRingEquivCuspAlg k).symm.toRingEquiv
      (RingEquiv.refl k[X]) hcompat
  exact (RingHom.finite_algebraMap).mpr inferInstance

/-- The original affine cusp parametrization is a finite scheme map. -/
theorem schemeMap_isFinite : IsFinite (schemeMap k) := by
  rw [schemeMap]
  rw [IsFinite.SpecMap_iff]
  exact cuspParam_finite k

#print axioms coordinateRing_isFractionRing
#print axioms coordinateRing_isFractionRing_canonical
#print axioms coordinateRing_isIntegralClosure_canonical
#print axioms coordinateRing_integralClosureEquiv
#print axioms coordinateRing_integralClosureSpecIso_over_cusp
#print axioms cuspParam_finite
#print axioms schemeMap_isFinite

end Pcf.Examples.PaperP.CuspOriginalFibre
