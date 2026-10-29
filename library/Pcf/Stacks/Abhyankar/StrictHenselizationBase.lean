/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationHenselian
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotient

/-!
# The local base map of the strict local-colimit construction

The canonical map from the original local ring to the localized pointed-etale colimit is local.
Consequently, an ideal contained in the original maximal ideal extends to an ideal contained in
the maximal ideal of the strict local colimit.  Applying the quotient theorem proves the
intrinsic strictly-henselian conclusion in Stacks Tag `05WS` for this construction.
-/

@[expose] public section

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

/-- The base map into the strict local colimit is a local homomorphism. -/
instance localColimit_base_isLocalHom :
    IsLocalHom (algebraMap R (LocalColimit R Ω)) := by
  apply ((IsLocalRing.local_hom_TFAE
    (algebraMap R (LocalColimit R Ω))).out 4 1).mp
  intro r hr
  rw [Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff]
  let e := residueFieldAlgEquiv (R := R) (Ω := Ω)
  apply e.injective
  rw [map_zero]
  change e (algebraMap R
    (IsLocalRing.ResidueField (LocalColimit R Ω)) r) = 0
  rw [e.commutes]
  rw [IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) Ω]
  change algebraMap (IsLocalRing.ResidueField R) Ω
    (IsLocalRing.residue R r) = 0
  have hr0 : IsLocalRing.residue R r = 0 :=
    (IsLocalRing.residue_eq_zero_iff r).mpr hr
  rw [hr0, map_zero]

/-- Ideals in the original maximal ideal extend inside the maximal ideal of the strict local
colimit. -/
theorem map_le_maximalIdeal_localColimit (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    I.map (algebraMap R (LocalColimit R Ω)) ≤
      IsLocalRing.maximalIdeal (LocalColimit R Ω) :=
  (Ideal.map_mono hI).trans
    (IsLocalRing.map_maximalIdeal_le (algebraMap R (LocalColimit R Ω)))

/-- The quotient of the constructed strict local colimit by an ideal extended from the base is
strictly henselian.  This is the intrinsic ring-theoretic conclusion of Stacks Tag `05WS`; the
remaining exact-tag comparison is an equivalence with the separately constructed strict
henselization of `R ⧸ I`. -/
theorem quotient_localColimit_strictlyHenselianLocalRing (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    StrictlyHenselianLocalRing
      (LocalColimit R Ω ⧸ I.map (algebraMap R (LocalColimit R Ω))) :=
  StrictlyHenselianLocalRing.quotient_of_le_maximalIdeal _
    (map_le_maximalIdeal_localColimit (R := R) (Ω := Ω) I hI)

end Pcf.Stacks.PointedEtaleNeighborhood
