/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationComparison
public import Pcf.Bounding.GlobalNormalizationNormal
public import Pcf.Bounding.GlobalNormalizationFinite
public import Pcf.Bounding.NormalizationSchemeBridge

/-!
# Actual normalized dynamics on the canonical global normalization

This file assembles the canonical normalization, its functorial lifted endomorphism,
normality, finite-type finiteness, and the finite-birational ramification comparison into
the exact two-carrier package used by the PCF argument.

For an integral finite-type scheme in characteristic zero and a finite dominant
endomorphism `g`, the result constructs:

* the canonical finite dominant normalization morphism;
* the finite dominant lifted endomorphism and its commuting square;
* actual divisor pushforwards with finite normalization fibres; and
* the actual stalk-defined unnormalized critical loci, including U1--U5.

No normality, finiteness, functoriality, ramification comparison, or PCF conclusion is
assumed for the normalization package.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

/-- Assemble the actual normalized/unnormalized divisor dynamics from affine finite-type
structures on the target. -/
def schemeGlobalNormalizationUnnormDyn
    (k : Type u) [Field k] [CharZero k]
    {A : Scheme.{u}} (g : A ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)] :
    SchemeNormalizationUnnormDyn A
      (SchemeDivisorPoint (schemeGlobalNormalization A)) := by
  letI : IsFinite (schemeGlobalNormalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k
  letI : IsLocallyNoetherian (schemeGlobalNormalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian (schemeGlobalNormalizationMap A)
  exact schemeNormalizationUnnormDynOfFiniteBirational k g
    (schemeGlobalNormalizationLift g) (schemeGlobalNormalizationMap A)
    (schemeGlobalNormalizationLift_comp g)

/-- Assemble the same package directly from a locally finite-type structure morphism to
the spectrum of a characteristic-zero field. -/
def schemeGlobalNormalizationUnnormDynOfFiniteType
    (k : Type u) [Field k] [CharZero k]
    {A : Scheme.{u}} (s : A ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (g : A ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))] :
    SchemeNormalizationUnnormDyn A
      (SchemeDivisorPoint (schemeGlobalNormalization A)) := by
  let φ (U : A.affineOpens) : k →+* Γ(A, U) :=
    (s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let (U : A.affineOpens) : Algebra k Γ(A, U) := (φ U).toAlgebra
  have (U : A.affineOpens) : Algebra.FiniteType k Γ(A, U) := by
    apply RingHom.finiteType_algebraMap.mp
    change (φ U).FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  exact schemeGlobalNormalizationUnnormDyn k g

#print axioms schemeGlobalNormalizationUnnormDyn
#print axioms schemeGlobalNormalizationUnnormDynOfFiniteType

end

end Pcf
