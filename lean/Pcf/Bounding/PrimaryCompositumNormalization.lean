/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryPureCompositum
public import Pcf.Bounding.PrimaryNormalizationFinite

/-!
# The actual normalization in a purely inseparable compositum

The finite pure alteration of the base function field in
`paper-p.tex`, Lemma `lem:primary-fibres`, produces the reduced
compositum of that field with the source function field. Its
normalization over each normal affine chart of the source is a finite
radicial morphism. This file applies the generic compositum proofs to
the actual affine normalization construction.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The normalization of a normal finite-type affine source in the
reduced compositum with a finite purely inseparable base alteration is
finite, universally injective, and surjective. -/
theorem pureCompositum_integralClosure_specMap_finite_radicial
    (k K E P R : Type u) [Field k] [Field K] [Field E] [Field P]
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    [Algebra R E] [IsFractionRing R E]
    [Algebra K E] [Algebra K P]
    [IsPurelyInseparable K P] [FiniteDimensional K P]
    (p : ℕ) (hp : p.Prime) [CharP k p] :
    letI : Field (pureCompositum K E P) := pureCompositumField K E P
    letI : Algebra R (pureCompositum K E P) :=
      inferInstance
    let f := Spec.map (CommRingCat.ofHom
      (algebraMap R (integralClosure R (pureCompositum K E P))))
    IsFinite f ∧ UniversallyInjective f ∧ Surjective f := by
  letI : Field (pureCompositum K E P) := pureCompositumField K E P
  letI : Algebra R (pureCompositum K E P) := inferInstance
  haveI : IsScalarTower R E (pureCompositum K E P) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : FiniteDimensional E (pureCompositum K E P) :=
    pureCompositum_finite K E P
  haveI : IsPurelyInseparable E (pureCompositum K E P) :=
    pureCompositum_isPurelyInseparable K E P
  exact integralClosure_specMap_finite_radicial k p hp R E
    (pureCompositum K E P)

#print axioms pureCompositum_integralClosure_specMap_finite_radicial

end
end Pcf.Bounding.PrimaryFibres
