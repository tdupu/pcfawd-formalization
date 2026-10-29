/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeMaximalSeparableStability

/-!
# Semilinear self-maps of integral-closure charts

A commuting pair of ring endomorphisms of a base ring and its field
extension preserves the actual integral closure. This is the affine
map needed to extend the restricted maximal separable function-field
endomorphism to the normalization in `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`.
-/

@[expose] public section

namespace Pcf

noncomputable section

open CategoryTheory AlgebraicGeometry

/-- A semilinear field endomorphism preserves the integral closure of
the base ring in the field. -/
theorem semilinear_integralClosure_mem
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    (a : R →+* R) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap R L).comp a)
    (x : integralClosure R L) :
    IsIntegral R (h (x : L)) :=
  IsIntegral.map_of_comp_eq a h hcomm.symm x.2

/-- The actual integral-closure ring map induced by a semilinear
field endomorphism. -/
def semilinearIntegralClosureMap
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    (a : R →+* R) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap R L).comp a) :
    integralClosure R L →+* integralClosure R L where
  toFun x := ⟨h (x : L), semilinear_integralClosure_mem R L a h hcomm x⟩
  map_one' := Subtype.ext h.map_one
  map_mul' x y := Subtype.ext (h.map_mul x y)
  map_zero' := Subtype.ext h.map_zero
  map_add' x y := Subtype.ext (h.map_add x y)

/-- On the ambient field, the integral-closure map is exactly the
original endomorphism. -/
theorem semilinearIntegralClosureMap_to_field
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    (a : R →+* R) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap R L).comp a) :
    (algebraMap (integralClosure R L) L).comp
        (semilinearIntegralClosureMap R L a h hcomm) =
      h.comp (algebraMap (integralClosure R L) L) := by
  ext x
  rfl

/-- The integral-closure map lies over the base-ring endomorphism. -/
theorem semilinearIntegralClosureMap_to_base
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    (a : R →+* R) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap R L).comp a) :
    (semilinearIntegralClosureMap R L a h hcomm).comp
        (algebraMap R (integralClosure R L)) =
      (algebraMap R (integralClosure R L)).comp a := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change h (algebraMap R L r) = algebraMap R L (a r)
  exact congrArg (fun u : R →+* L => u r) hcomm

/-- If the base self-map and the integral-closure chart are finite,
then the induced endomorphism of the actual integral closure is finite.
This is the affine finiteness step in the source's construction. -/
theorem semilinearIntegralClosureMap_finite
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    [Module.Finite R (integralClosure R L)]
    (a : R →+* R) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap R L).comp a)
    (ha : a.Finite) :
    (semilinearIntegralClosureMap R L a h hcomm).Finite := by
  let i := algebraMap R (integralClosure R L)
  have hi : i.Finite := RingHom.finite_algebraMap.mpr inferInstance
  have hc : ((semilinearIntegralClosureMap R L a h hcomm).comp i).Finite := by
    rw [semilinearIntegralClosureMap_to_base]
    exact RingHom.Finite.comp hi ha
  exact RingHom.Finite.of_comp_finite hc

/-- The corresponding self-map of the affine normalization chart is
a finite morphism of schemes. -/
theorem semilinearIntegralClosureMap_spec_isFinite
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    [Module.Finite R (integralClosure R L)]
    (a : R →+* R) (h : L →+* L)
    (hcomm : h.comp (algebraMap R L) = (algebraMap R L).comp a)
    (ha : a.Finite) :
    IsFinite (Spec.map (CommRingCat.ofHom
      (semilinearIntegralClosureMap R L a h hcomm))) := by
  exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
    (semilinearIntegralClosureMap R L a h hcomm))).mpr
      (semilinearIntegralClosureMap_finite R L a h hcomm ha)

#print axioms semilinear_integralClosure_mem
#print axioms semilinearIntegralClosureMap
#print axioms semilinearIntegralClosureMap_to_field
#print axioms semilinearIntegralClosureMap_to_base
#print axioms semilinearIntegralClosureMap_finite
#print axioms semilinearIntegralClosureMap_spec_isFinite

end
end Pcf
