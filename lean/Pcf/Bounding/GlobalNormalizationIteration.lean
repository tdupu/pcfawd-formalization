/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationMorphism
public import Pcf.Bounding.SchemeIteration

/-!
# Iteration on the canonical global normalization

The canonical normalization lift preserves identity, composition, and all powers.
Consequently the actual normalized divisor dynamics of a scheme iterate is the
abstract iterate of its normalized dynamics. In characteristic zero, the
normalized postcritical set and postcritical finiteness are unchanged by every
positive iterate, including for possibly nonnormal integral schemes.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X]

/-- The generic-point map of the identity is the identity. -/
@[simp]
theorem schemeGenericMorphism_id :
    schemeGenericMorphism (𝟙 X) = 𝟙 (Spec X.functionField) := by
  apply (cancel_mono (schemeGenericInclusion X)).mp
  simp only [schemeGenericMorphism_comp, Category.comp_id, Category.id_comp]

/-- The canonical global-normalization lift preserves the identity. -/
@[simp]
theorem schemeGlobalNormalizationMorphism_id :
    schemeGlobalNormalizationMorphism (𝟙 X) = 𝟙 (schemeGlobalNormalization X) := by
  symm
  apply schemeGlobalNormalizationMorphism_unique
  · simp
  · simp

/-- The endomorphism form of the canonical lift preserves the identity. -/
@[simp]
theorem schemeGlobalNormalizationLift_id :
    schemeGlobalNormalizationLift (𝟙 X) = 𝟙 (schemeGlobalNormalization X) :=
  schemeGlobalNormalizationMorphism_id

/-- The endomorphism form of the canonical lift preserves composition. -/
theorem schemeGlobalNormalizationLift_comp_lift (f g : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g] :
    schemeGlobalNormalizationLift (f ≫ g) =
      schemeGlobalNormalizationLift f ≫ schemeGlobalNormalizationLift g :=
  (schemeGlobalNormalizationMorphism_comp_morphism f g).symm

/-- The canonical normalization morphism of every power is the power of the
canonical normalization morphism. No finite-type assumption is needed. -/
theorem schemeGlobalNormalizationMorphism_pow (f : X ⟶ X)
    [IsFinite f] [IsDominant f] (m : ℕ) :
    schemeGlobalNormalizationMorphism (End.of f ^ m).asHom =
      (End.of (schemeGlobalNormalizationMorphism f) ^ m).asHom := by
  induction m with
  | zero => simpa only [pow_zero, End.one_asHom] using schemeGlobalNormalizationMorphism_id
  | succ m ih =>
      simp only [pow_succ, End.mul_asHom,
        ← schemeGlobalNormalizationMorphism_comp_morphism, ih]

/-- The canonical lift commutes with all nonnegative iterates. -/
theorem schemeGlobalNormalizationLift_pow (f : X ⟶ X)
    [IsFinite f] [IsDominant f] (m : ℕ) :
    schemeGlobalNormalizationLift (End.of f ^ m).asHom =
      (End.of (schemeGlobalNormalizationLift f) ^ m).asHom :=
  schemeGlobalNormalizationMorphism_pow f m

section FiniteType

variable (k : Type u) [Field k] [CharZero k]
  [IsLocallyNoetherian X] [NoetherianSpace X]
  [CharZero (X.presheaf.stalk (genericPoint X))]
  [∀ U : X.affineOpens, Algebra k Γ(X, U)]
  [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)]
  (f : X ⟶ X) [IsFinite f] [IsDominant f]

/-- The upstairs dynamics in the canonical normalization package is the actual
characteristic-zero divisor dynamics of its lifted morphism. -/
theorem schemeGlobalNormalizationUnnormalizedDynamics_normalized_eq
    [IsFinite (schemeGlobalNormalizationMap X)] :
    (schemeGlobalNormalizationUnnormalizedDynamics k f).normalized =
      divisorDynamicsOfFiniteDominantNormalCharZero (schemeGlobalNormalizationLift f) := rfl

/-- The normalized divisor dynamics of an actual scheme power is exactly the
abstract iterate, with its actual stalk ramification indices. -/
theorem schemeGlobalNormalizationUnnormalizedDynamics_normalized_pow (m : ℕ) :
    (schemeGlobalNormalizationUnnormalizedDynamics k (End.of f ^ m).asHom).normalized =
      ((schemeGlobalNormalizationUnnormalizedDynamics k f).normalized).iterate m := by
  let := schemeGlobalNormalizationMap_isFinite_of_affineFiniteType X k
  rw [schemeGlobalNormalizationUnnormalizedDynamics_normalized_eq,
    schemeGlobalNormalizationUnnormalizedDynamics_normalized_eq]
  simpa only [schemeGlobalNormalizationLift_pow] using
    divisorDynamicsOfFiniteDominantNormalCharZero_pow_eq_iterate (schemeGlobalNormalizationLift f) m

/-- The postcritical set defined using the canonical normalized branch locus is
unchanged by every positive iterate of the actual scheme morphism. -/
theorem schemeNormalizedPostcriticalSet_pow (m : ℕ) (hm : 1 ≤ m) :
    schemeNormalizedPostcriticalSet k (End.of f ^ m).asHom = schemeNormalizedPostcriticalSet k f := by
  rw [schemeNormalizedPostcriticalSet_eq_normalization_image,
    schemeNormalizedPostcriticalSet_eq_normalization_image,
    schemeGlobalNormalizationUnnormalizedDynamics_normalized_pow, DivisorDynamics.postcriticalSet_iterate _ hm]
  exact congrArg (fun ν ↦ ν '' (schemeGlobalNormalizationUnnormalizedDynamics k f).normalized.postcriticalSet)
    (funext fun Q ↦ Subtype.ext (by
      simp only [schemeGlobalNormalizationUnnormalizedDynamics_normalization_val]))

/-- Normalized postcritical finiteness is equivalent to that of any positive
iterate, without assuming normality of the original scheme. -/
theorem isNormalizedPCF_pow_iff (m : ℕ) (hm : 1 ≤ m) :
    IsNormalizedPCF k (End.of f ^ m).asHom ↔ IsNormalizedPCF k f := by
  unfold IsNormalizedPCF
  rw [schemeNormalizedPostcriticalSet_pow k f m hm]

end FiniteType

#check @schemeGlobalNormalizationMorphism_pow
#check @schemeGlobalNormalizationUnnormalizedDynamics_normalized_pow
#check @schemeNormalizedPostcriticalSet_pow
#check @isNormalizedPCF_pow_iff
#print axioms schemeGenericMorphism_id
#print axioms schemeGlobalNormalizationMorphism_id
#print axioms schemeGlobalNormalizationLift_id
#print axioms schemeGlobalNormalizationLift_comp_lift
#print axioms schemeGlobalNormalizationMorphism_pow
#print axioms schemeGlobalNormalizationLift_pow
#print axioms schemeGlobalNormalizationUnnormalizedDynamics_normalized_eq
#print axioms schemeGlobalNormalizationUnnormalizedDynamics_normalized_pow
#print axioms schemeNormalizedPostcriticalSet_pow
#print axioms isNormalizedPCF_pow_iff

end

end Pcf
