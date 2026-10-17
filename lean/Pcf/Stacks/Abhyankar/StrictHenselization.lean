/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Strictly henselian local rings: reusable finite-etale consequences

Mathlib does not yet provide a strict henselization construction.  This file therefore isolates
the intrinsic property of a strictly henselian local ring—being henselian with separably closed
residue field—and proves the finite-etale consequences available from the current library.

The local-component theorem below is one of the two ingredients in the usual strictly henselian
splitting theorem: a finite etale algebra which is already local is the base ring.  The other
ingredient, decomposition of every finite etale algebra over a henselian local ring into local
factors, is not present in the pinned Mathlib and is deliberately not assumed here.

This file does not claim Stacks Tag `04HN`: that tag is the scheme-theoretic assertion that a
finite etale morphism splits after passing to an etale neighbourhood of a specified point.  It
also does not claim Tags `05WS` or `06LN`, whose statements require an actual strict
henselization object.
-/

@[expose] public section

universe u

open TensorProduct

namespace Pcf.Stacks

/-- A local ring is strictly henselian if it is henselian and its residue field is separably
closed.  This intrinsic property is useful independently of a chosen strict henselization. -/
class StrictlyHenselianLocalRing (R : Type u) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)

attribute [instance] StrictlyHenselianLocalRing.toHenselianLocalRing
  StrictlyHenselianLocalRing.isSepClosed_residueField

/-- The closed fiber of a finite etale algebra over a strictly henselian local ring is a finite
product of copies of the residue field.

This is the residue-field part of finite-etale splitting.  It follows from Mathlib's
classification of finite etale algebras over a separably closed field. -/
theorem StrictlyHenselianLocalRing.isFiniteSplit_residueField_tensorProduct
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] [Module.Finite R S] [Algebra.Etale R S] :
    Algebra.IsFiniteSplit (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S) := by
  infer_instance

/-- A finite etale *local* algebra over a strictly henselian local ring has rank one and its
algebra map is bijective.

The proof identifies the residue-field extension using separable closedness, transfers its
dimension to the original finite etale extension, and then applies the rank-one criterion for
finite free algebras.  The `IsLocalHom` hypothesis says that the chosen local component lies over
the closed point. -/
theorem StrictlyHenselianLocalRing.bijective_algebraMap_of_finite_etale_local
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Algebra.Etale R S] :
    Function.Bijective (algebraMap R S) := by
  let _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hresidue : Function.Bijective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :=
    IsSepClosed.algebraMap_bijective _ _
  have hresidueRank : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) = 1 :=
    Module.finrank_of_bijective_algebraMap hresidue
  have hRank : Module.finrank R S = 1 := by
    rw [IsLocalRing.finrank_eq_finrank_residueField]
    exact hresidueRank
  let _ : Module.Free R S := Module.free_of_flat_of_isLocalRing
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hRank

/-- A finite etale local algebra over a strictly henselian local ring, with its local map, is
canonically isomorphic to the base ring as an algebra. -/
noncomputable def StrictlyHenselianLocalRing.finiteEtaleLocalAlgEquiv
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Algebra.Etale R S] :
    S ≃ₐ[R] R :=
  (AlgEquiv.ofBijective (Algebra.ofId R S)
    (StrictlyHenselianLocalRing.bijective_algebraMap_of_finite_etale_local R S)).symm

/-- Regularity transfers to a finite etale local component over a strictly henselian local ring.

This follows from the preceding algebra equivalence.  It is a local input for the regularity
part of the Abhyankar proof, but is not Tag `06LN`: that tag concerns the (strict) henselization
itself, not a finite etale local algebra. -/
theorem StrictlyHenselianLocalRing.isRegularRing_finite_etale_local
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] [IsRegularRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Algebra.Etale R S] :
    IsRegularRing S := by
  let e := StrictlyHenselianLocalRing.finiteEtaleLocalAlgEquiv R S
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

end Pcf.Stacks
