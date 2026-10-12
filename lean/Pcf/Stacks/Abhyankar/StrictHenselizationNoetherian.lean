/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Pcf.Stacks.Abhyankar.StrictHenselizationMaximalIdeal

/-!
# Noetherianity of the strict local colimit

This file isolates the completion step in Stacks Tag `06LJ`.  Once the maximal-adic completion
of the strict local colimit is known to be Noetherian and flat over the colimit, faithful-flat
descent proves that the colimit itself is Noetherian.
-/

universe u

namespace Pcf.Stacks

/-- A local ring with finitely generated maximal ideal is Noetherian if its maximal-adic
completion is Noetherian and flat over the ring. -/
theorem isNoetherianRing_of_maximalAdicCompletion
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hfg : (IsLocalRing.maximalIdeal A).FG)
    (hnoeth : IsNoetherianRing
      (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hflat : Module.Flat A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    IsNoetherianRing A := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let _ : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hfg
  let _ : IsLocalHom (algebraMap A C) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  let _ : Module.Flat A C := hflat
  let _ : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let _ : IsNoetherianRing C := hnoeth
  rw [isNoetherianRing_iff]
  apply Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (R := A) (A := C) (M := A)
  exact isNoetherian_of_linearEquiv
    (Algebra.TensorProduct.rid A C C).symm.toLinearEquiv

namespace PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Field Ω] [Algebra R Ω]
  [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

/-- Noetherianity of the strict local colimit reduces to the two completion facts in the proof
of Stacks Tag `06LJ`: its completion is Noetherian and the completion map is flat. -/
theorem localColimit_isNoetherianRing_of_completion
    (hnoeth : IsNoetherianRing
      (AdicCompletion
        (IsLocalRing.maximalIdeal (LocalColimit R Ω))
        (LocalColimit R Ω)))
    (hflat : Module.Flat (LocalColimit R Ω)
      (AdicCompletion
        (IsLocalRing.maximalIdeal (LocalColimit R Ω))
        (LocalColimit R Ω))) :
    IsNoetherianRing (LocalColimit R Ω) := by
  apply isNoetherianRing_of_maximalAdicCompletion
    (LocalColimit R Ω) _ hnoeth hflat
  rw [← map_maximalIdeal_localColimit (R := R) (Ω := Ω)]
  exact (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing.map
    (algebraMap R (LocalColimit R Ω))

end PointedEtaleNeighborhood

end Pcf.Stacks
