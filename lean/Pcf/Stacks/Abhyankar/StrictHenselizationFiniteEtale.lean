/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationResidue
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Etale.Weakly

/-!
# Finite etale local algebras over the localized pointed-etale colimit

The residue-field computation for the localized filtered colimit already forces every finite
etale *local* algebra over it to have rank one.  Thus its algebra map is an isomorphism.  This is
one of the two finite-etale consequences needed for strict henselianity; the remaining issue is
the existence of local-factor decompositions for arbitrary finite etale algebras.
-/

@[expose] public section

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

/-- A finite etale local algebra over the localized pointed-etale colimit has rank one and its
algebra map is bijective. -/
theorem bijective_algebraMap_finiteEtale_local
    (S : Type u) [CommRing S] [Algebra (LocalColimit R Ω) S]
    [IsLocalRing S] [IsLocalHom (algebraMap (LocalColimit R Ω) S)]
    [Module.Finite (LocalColimit R Ω) S] [Algebra.Etale (LocalColimit R Ω) S] :
    Function.Bijective (algebraMap (LocalColimit R Ω) S) := by
  let _ : IsSepClosed (IsLocalRing.ResidueField (LocalColimit R Ω)) :=
    residueField_isSepClosed (R := R) (Ω := Ω)
  let _ : Module.FaithfullyFlat (LocalColimit R Ω) S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hresidue : Function.Bijective
      (algebraMap (IsLocalRing.ResidueField (LocalColimit R Ω))
        (IsLocalRing.ResidueField S)) :=
    IsSepClosed.algebraMap_bijective _ _
  have hresidueRank : Module.finrank (IsLocalRing.ResidueField (LocalColimit R Ω))
      (IsLocalRing.ResidueField S) = 1 :=
    Module.finrank_of_bijective_algebraMap hresidue
  have hRank : Module.finrank (LocalColimit R Ω) S = 1 := by
    rw [IsLocalRing.finrank_eq_finrank_residueField]
    exact hresidueRank
  let _ : Module.Free (LocalColimit R Ω) S := Module.free_of_flat_of_isLocalRing
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hRank

/-- A finite etale local algebra over the localized pointed-etale colimit is isomorphic to the
base as an algebra. -/
noncomputable def finiteEtaleLocalAlgEquiv
    (S : Type u) [CommRing S] [Algebra (LocalColimit R Ω) S]
    [IsLocalRing S] [IsLocalHom (algebraMap (LocalColimit R Ω) S)]
    [Module.Finite (LocalColimit R Ω) S] [Algebra.Etale (LocalColimit R Ω) S] :
    S ≃ₐ[LocalColimit R Ω] LocalColimit R Ω :=
  (AlgEquiv.ofBijective (Algebra.ofId (LocalColimit R Ω) S)
    (bijective_algebraMap_finiteEtale_local (R := R) (Ω := Ω) S)).symm

end Pcf.Stacks.PointedEtaleNeighborhood
