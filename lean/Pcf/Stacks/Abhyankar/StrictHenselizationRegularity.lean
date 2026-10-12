/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.RegularLocalRing.Defs
import Pcf.Stacks.Abhyankar.StrictHenselizationNoetherian

/-!
# The final regularity step for strict henselization

Stacks Tag `06LN` compares the regularity of a Noetherian local ring with its henselization and
strict henselization.  Its last implication uses two earlier structural facts: the target is
Noetherian, its maximal ideal is extended from the base, and its Krull dimension is unchanged.

This file formalizes that last implication in reusable form and specializes it to the
pointed-etale-colimit construction.  The terminal theorem supplies target Noetherianity from
the completion route of Stacks Tag `06LJ` (using Tags `05GH` and `032B` internally), so its only
remaining completion input is flatness over the strict local colimit.

The endpoint is precisely the forward implication `R` regular implies `Rˢʰ` regular used by the
PCFAWD proof.  It does not package the converse or the comparison with `Rʰ` from the full
three-way equivalence in Tag `06LN`: doing so for this concrete construction additionally requires
the faithfully-flat cotangent-space dimension comparison.  This is a scope boundary, not an
extra hypothesis of the forward endpoint below.
-/

universe u

namespace Pcf.Stacks

/-- The forward regularity implication in the proof of Stacks Tag `06LN`: if a local extension
has extended maximal ideal and unchanged Krull dimension, regularity ascends. -/
theorem IsRegularLocalRing.of_map_maximalIdeal_eq_of_ringKrullDim_eq
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S)
    (hdim : ringKrullDim R = ringKrullDim S) :
    IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hmax]
  calc
    (↑((IsLocalRing.maximalIdeal R).map (algebraMap R S)).spanFinrank : WithBot ℕ∞) ≤
        ↑(IsLocalRing.maximalIdeal R).spanFinrank := by
      exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
        (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    _ = ringKrullDim R :=
      (isRegularLocalRing_iff R).mp (inferInstance : IsRegularLocalRing R)
    _ = ringKrullDim S := hdim

namespace PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Once Noetherianity, extension of the maximal ideal, and dimension invariance have been proved
for the constructed strict henselization, regularity follows formally.  This is the exact final
step of the `R → Rˢʰ` direction of Stacks Tag `06LN`. -/
theorem localColimit_isRegularLocalRing_of_maximalIdeal_eq_of_ringKrullDim_eq
    [IsRegularLocalRing R] [IsNoetherianRing (LocalColimit R Ω)]
    (hmax : (IsLocalRing.maximalIdeal R).map
        (algebraMap R (LocalColimit R Ω)) =
      IsLocalRing.maximalIdeal (LocalColimit R Ω))
    (hdim : ringKrullDim R = ringKrullDim (LocalColimit R Ω)) :
    IsRegularLocalRing (LocalColimit R Ω) :=
  IsRegularLocalRing.of_map_maximalIdeal_eq_of_ringKrullDim_eq
    R (LocalColimit R Ω) hmax hdim

/-- The strict local colimit of a regular local ring is regular once its Noetherianity is known. -/
theorem localColimit_isRegularLocalRing_of_isNoetherianRing
    [IsRegularLocalRing R]
    [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
    [IsSepClosure (IsLocalRing.ResidueField R) Ω]
    [IsNoetherianRing (LocalColimit R Ω)] :
    IsRegularLocalRing (LocalColimit R Ω) :=
  localColimit_isRegularLocalRing_of_maximalIdeal_eq_of_ringKrullDim_eq
    (map_maximalIdeal_localColimit (R := R) (Ω := Ω))
    (ringKrullDim_localColimit (R := R) (Ω := Ω))

/-- The `R → Rˢʰ` regularity endpoint of Stacks Tag `06LN` for the pointed-etale-colimit
construction.  Flatness of the maximal-adic completion supplies Noetherianity through Tag `06LJ`;
the extended-maximal-ideal and dimension comparisons then identify regularity. -/
theorem localColimit_isRegularLocalRing_of_completion_flat
    [IsRegularLocalRing R]
    [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
    [IsSepClosure (IsLocalRing.ResidueField R) Ω]
    (hflat : Module.Flat (LocalColimit R Ω)
      (AdicCompletion
        (IsLocalRing.maximalIdeal (LocalColimit R Ω))
        (LocalColimit R Ω))) :
    IsRegularLocalRing (LocalColimit R Ω) := by
  let _ : IsNoetherianRing (LocalColimit R Ω) :=
    localColimit_isNoetherianRing_of_completion hflat
  exact localColimit_isRegularLocalRing_of_isNoetherianRing

#print axioms IsRegularLocalRing.of_map_maximalIdeal_eq_of_ringKrullDim_eq
#print axioms localColimit_isRegularLocalRing_of_maximalIdeal_eq_of_ringKrullDim_eq
#print axioms localColimit_isRegularLocalRing_of_isNoetherianRing
#print axioms localColimit_isRegularLocalRing_of_completion_flat

end PointedEtaleNeighborhood

end Pcf.Stacks
