/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeMaximalSeparableGenericChart

/-!
# Integral closure under an integral base change

When `R → S` is integral and both rings act compatibly on a common
field, an element of the field is integral over `R` exactly when it is
integral over `S`. This identifies the affine charts of a normalization
before and after postcomposition with a finite base map. In the application
to `paper-p.tex`, Lemma `lem:pcf-transfer-charp`, the `R` action is the
twisted action pulled back through the base self-map.
-/

@[expose] public section

open AlgebraicGeometry

namespace Pcf

noncomputable section

universe u

set_option linter.style.haveILetI false

/-- Integrality over a ring and over an integral extension of that ring
coincide inside a common algebra. -/
theorem isIntegral_iff_of_integral_base
    (R S L : Type*) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [Algebra.IsIntegral R S]
    (x : L) : IsIntegral R x ↔ IsIntegral S x := by
  constructor
  · exact IsIntegral.tower_top
  · exact isIntegral_trans x

/-- Canonical ring equivalence of integral closures across an integral
base extension, realized by the identity on their common ambient algebra. -/
def integralClosureIntegralBaseEquiv
    (R S L : Type*) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [Algebra.IsIntegral R S] :
    integralClosure R L ≃+* integralClosure S L where
  toFun x := ⟨x.1, (isIntegral_iff_of_integral_base R S L x.1).mp x.2⟩
  invFun x := ⟨x.1, (isIntegral_iff_of_integral_base R S L x.1).mpr x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Both integral-closure embeddings into the ambient algebra agree
after the canonical equivalence. -/
theorem integralClosureIntegralBaseEquiv_to_ambient
    (R S L : Type*) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [Algebra.IsIntegral R S] :
    (algebraMap (integralClosure S L) L).comp
        (integralClosureIntegralBaseEquiv R S L).toRingHom =
      algebraMap (integralClosure R L) L := by
  ext x
  rfl

#print axioms isIntegral_iff_of_integral_base
#print axioms integralClosureIntegralBaseEquiv
#print axioms integralClosureIntegralBaseEquiv_to_ambient

/-- On an affine open `U` of a finite dominant scheme self-map, the
integral closure for the *pulled-back* `Γ(U)` action is the same as the
integral closure for the coordinate ring of `f⁻¹ U`. This is the chart
comparison needed to identify the normalization of a generic inclusion
postcomposed with `f` with the original normalization. -/
def schemeFiniteSelfMap_twistedIntegralClosureEquiv
    (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (M : Type u) [Field M] [Algebra X.functionField M]
    (U : X.affineOpens) [Nonempty (U : X.Opens)] :
    let V := finitePreimageAffine f U
    letI : Nonempty (V : X.Opens) := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ (U : X.Opens)
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
        (by simpa using ‹Nonempty (U : X.Opens)›)
    letI : Algebra Γ(X, U) Γ(X, V) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(X, V) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, U) M :=
      ((algebraMap Γ(X, V) M).comp (f.app U).hom).toAlgebra
    integralClosure Γ(X, U) M ≃+* integralClosure Γ(X, V) M := by
  let V := finitePreimageAffine f U
  have hmem : f (genericPoint X) ∈ (U : X.Opens) := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : X.Opens)›)
  letI : Nonempty (V : X.Opens) := ⟨⟨genericPoint X, hmem⟩⟩
  letI : Algebra Γ(X, U) Γ(X, V) := (f.app U).hom.toAlgebra
  letI : Algebra Γ(X, V) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Algebra Γ(X, U) M :=
    ((algebraMap Γ(X, V) M).comp (f.app U).hom).toAlgebra
  letI : Module.Finite Γ(X, U) Γ(X, V) := moduleFinite_finitePreimageAffine f U
  letI : Algebra.IsIntegral Γ(X, U) Γ(X, V) := Algebra.IsIntegral.of_finite _ _
  letI : IsScalarTower Γ(X, U) Γ(X, V) M := IsScalarTower.of_algebraMap_eq' rfl
  exact integralClosureIntegralBaseEquiv Γ(X, U) Γ(X, V) M

#print axioms schemeFiniteSelfMap_twistedIntegralClosureEquiv

end
end Pcf
