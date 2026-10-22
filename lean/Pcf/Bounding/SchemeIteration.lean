/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDynamics

/-!
# Actual divisor dynamics and scheme iterates

This file identifies the `DivisorDynamics` constructed from an actual scheme iterate with the
abstract iterate of the `DivisorDynamics` constructed from the original morphism.  The step map is
identified on the underlying scheme points, and the ramification function is identified
by the stalk ramification tower theorem.  The remaining structure fields are propositions,
so proof irrelevance completes the equality.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

/-- Two divisorial dynamical systems with the same step and ramification functions are
equal.  The positivity, lying-over, and branch-finiteness fields are propositions. -/
theorem DivisorDynamics.ext_of_step_ramificationIdx {P : Type u} {D E : DivisorDynamics P}
    (hstep : D.step = E.step) (hram : D.ramificationIdx = E.ramificationIdx) : D = E := by
  cases D
  cases E
  simp_all

/-- The actual divisor dynamics of a scheme iterate is the abstract iterate of the
actual divisor dynamics of the original morphism. -/
theorem divisorDynamicsOfFiniteDominantNormal_pow_eq_iterate
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorNonEtaleLocus f).Finite) (m : ℕ)
    (hcritm : (schemeDivisorNonEtaleLocus (CategoryTheory.End.of f ^ m).asHom).Finite) :
    divisorDynamicsOfFiniteDominantNormal (CategoryTheory.End.of f ^ m).asHom hcritm =
      (divisorDynamicsOfFiniteDominantNormal f hcrit).iterate m := by
  apply DivisorDynamics.ext_of_step_ramificationIdx
  · funext x
    apply Subtype.ext
    change (CategoryTheory.End.of f ^ m).asHom.base x.1 =
      (((divisorDynamicsOfFiniteDominantNormal f hcrit).step)^[m] x).1
    exact (divisorDynamicsOfFiniteDominantNormal_iterate_step_val f hcrit m x).symm
  · funext x
    change schemeDivisorRamificationIdx (CategoryTheory.End.of f ^ m).asHom x =
      (divisorDynamicsOfFiniteDominantNormal f hcrit).iterateRamificationIdx m x
    exact (divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx f hcrit m x).symm

/-- Characteristic-zero specialization, with critical-locus finiteness constructed
canonically on both sides. -/
theorem divisorDynamicsOfFiniteDominantNormalCharZero_pow_eq_iterate
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X] [CharZero (X.presheaf.stalk (genericPoint X))]
    (m : ℕ) :
    divisorDynamicsOfFiniteDominantNormalCharZero (CategoryTheory.End.of f ^ m).asHom =
      (divisorDynamicsOfFiniteDominantNormalCharZero f).iterate m :=
  divisorDynamicsOfFiniteDominantNormal_pow_eq_iterate f
    (schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale f
      ⟨genericPoint X,
        formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero f⟩)
    m
    (schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale
      (CategoryTheory.End.of f ^ m).asHom
      (exists_formallyEtale_stalk_iterate_of_exists f
        ⟨genericPoint X,
          formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero f⟩ m))

set_option linter.style.haveILetI false in
/-- Generic separability of a finite dominant self-map is preserved by
iteration, in any characteristic. This supplies the separable part of
`paper-p.tex`, Lemma `lem:prime-to-p-compose`; the prime-to-`p` degree
assertion is a separate field-theoretic obligation. -/
theorem isGenericallySeparable_pow
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f] [IsIntegral X]
    (hsep : IsGenericallySeparable f) (m : ℕ) :
    IsGenericallySeparable (CategoryTheory.End.of f ^ m).asHom := by
  have hgp : f (genericPoint X) = genericPoint X :=
    map_genericPoint_eq_of_isDominant f
  have hfg := formallyEtale_stalkMap_genericPoint_of_finite_dominant_separable f hsep
  have hiter : ∀ n,
      ((CategoryTheory.End.of f ^ n).asHom.stalkMap
        (genericPoint X)).hom.FormallyEtale := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero]
        change ((𝟙 X : X ⟶ X).stalkMap (genericPoint X)).hom.FormallyEtale
        rw [Scheme.Hom.stalkMap_id]
        change (RingHom.id _).FormallyEtale
        rw [RingHom.FormallyEtale]
        infer_instance
    | succ n ih =>
        rw [pow_succ, CategoryTheory.End.mul_asHom]
        change ((f ≫ (CategoryTheory.End.of f ^ n).asHom).stalkMap
          (genericPoint X)).hom.FormallyEtale
        rw [Scheme.Hom.stalkMap_comp]
        change ((f.stalkMap (genericPoint X)).hom.comp
          (((CategoryTheory.End.of f ^ n).asHom.stalkMap
            (f (genericPoint X))).hom)).FormallyEtale
        have hi : (((CategoryTheory.End.of f ^ n).asHom.stalkMap
            (f (genericPoint X))).hom).FormallyEtale := by
          rw [hgp]
          exact ih
        exact RingHom.FormallyEtale.comp hi hfg
  letI : IsFinite (CategoryTheory.End.of f ^ m).asHom := isFinite_end_pow f m
  letI : IsDominant (CategoryTheory.End.of f ^ m).asHom := isDominant_end_pow f m
  exact isGenericallySeparable_of_formallyEtale_generic
    (CategoryTheory.End.of f ^ m).asHom (hiter m)

/-- The actual index-only divisor dynamics of a generically separable
self-map commute with iteration. The characteristic-`p` branch comparison
still requires residue-separability at every divisor. -/
theorem divisorDynamicsOfFiniteDominantNormalSeparable_pow_eq_iterate
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) (m : ℕ) :
    divisorDynamicsOfFiniteDominantNormalSeparable
      (CategoryTheory.End.of f ^ m).asHom (isGenericallySeparable_pow f hsep m) =
      (divisorDynamicsOfFiniteDominantNormalSeparable f hsep).iterate m := by
  unfold divisorDynamicsOfFiniteDominantNormalSeparable
    divisorDynamicsOfFiniteDominantNormalNoetherian
    divisorDynamicsOfFiniteDominantNormalOfExistsFormallyEtale
  exact divisorDynamicsOfFiniteDominantNormal_pow_eq_iterate f _ m _

#print axioms DivisorDynamics.ext_of_step_ramificationIdx
#print axioms divisorDynamicsOfFiniteDominantNormal_pow_eq_iterate
#print axioms divisorDynamicsOfFiniteDominantNormalCharZero_pow_eq_iterate

end Pcf
