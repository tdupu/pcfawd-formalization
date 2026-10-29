/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stacks statements used by the projective Jacobian proof

The statements were checked against the live Stacks tags on 2026-10-28.
The algebra structures encode the indicated commutative ring homomorphisms.
-/

@[expose] public section
namespace Pcf.PaperCharZero
universe u v

/-- Stacks Lemma 10.31.4(3): a finite type algebra over a Noetherian ring
is of finite presentation. The other two module clauses are outside this declaration. -/
@[stacks 00FP "clause (3): finite type algebras"]
theorem projFinitePresentation_of_finiteType_noetherian
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [Algebra.FiniteType R S] : Algebra.FinitePresentation R S :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Stacks Lemma 10.150.3: for a ring map of finite presentation,
formal étaleness and étaleness are equivalent. -/
@[stacks 00UR]
theorem projFormallyEtale_iff_etale_of_finitePresentation
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    Algebra.FormallyEtale R S ↔ Algebra.Etale R S := by
  constructor
  · intro h
    exact ⟨h, inferInstance⟩
  · intro h
    exact h.formallyEtale

#print axioms projFinitePresentation_of_finiteType_noetherian
#print axioms projFormallyEtale_iff_etale_of_finitePresentation
end Pcf.PaperCharZero
