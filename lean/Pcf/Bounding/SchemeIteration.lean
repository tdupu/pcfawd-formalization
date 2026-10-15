/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDynamics

/-!
# Actual divisor dynamics and scheme iterates

This file identifies the `DivDyn` constructed from an actual scheme iterate with the
abstract iterate of the `DivDyn` constructed from the original morphism.  The step map is
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
theorem DivDyn.ext_of_step_ram {P : Type u} {D E : DivDyn P}
    (hstep : D.step = E.step) (hram : D.ram = E.ram) : D = E := by
  cases D
  cases E
  simp_all

/-- The actual divisor dynamics of a scheme iterate is the abstract iterate of the
actual divisor dynamics of the original morphism. -/
theorem divDynOfFiniteDominantNormal_pow_eq_iter
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorCrit1 f).Finite) (m : ℕ)
    (hcritm : (schemeDivisorCrit1 (CategoryTheory.End.of f ^ m).asHom).Finite) :
    divDynOfFiniteDominantNormal (CategoryTheory.End.of f ^ m).asHom hcritm =
      (divDynOfFiniteDominantNormal f hcrit).iter m := by
  apply DivDyn.ext_of_step_ram
  · funext x
    apply Subtype.ext
    change (CategoryTheory.End.of f ^ m).asHom.base x.1 =
      (((divDynOfFiniteDominantNormal f hcrit).step)^[m] x).1
    exact (divDynOfFiniteDominantNormal_iterate_step_val f hcrit m x).symm
  · funext x
    change schemeDivisorRam (CategoryTheory.End.of f ^ m).asHom x =
      (divDynOfFiniteDominantNormal f hcrit).iterRam m x
    exact (divDynOfFiniteDominantNormal_iterRam f hcrit m x).symm

/-- Characteristic-zero specialization, with critical-locus finiteness constructed
canonically on both sides. -/
theorem divDynOfFiniteDominantNormalCharZero_pow_eq_iter
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X] [CharZero (X.presheaf.stalk (genericPoint X))]
    (m : ℕ) :
    divDynOfFiniteDominantNormalCharZero (CategoryTheory.End.of f ^ m).asHom =
      (divDynOfFiniteDominantNormalCharZero f).iter m :=
  divDynOfFiniteDominantNormal_pow_eq_iter f
    (schemeDivisorCrit1_finite_of_exists_formallyEtale f
      ⟨genericPoint X,
        formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero f⟩)
    m
    (schemeDivisorCrit1_finite_of_exists_formallyEtale
      (CategoryTheory.End.of f ^ m).asHom
      (exists_formallyEtale_stalk_iterate_of_exists f
        ⟨genericPoint X,
          formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero f⟩ m))

#print axioms DivDyn.ext_of_step_ram
#print axioms divDynOfFiniteDominantNormal_pow_eq_iter
#print axioms divDynOfFiniteDominantNormalCharZero_pow_eq_iter

end Pcf
