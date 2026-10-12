/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.Module
import Pcf.Stacks.Abhyankar.StrictHenselizationMaximalIdeal

/-!
# Noetherianity of the strict local colimit

This file isolates the completion step in Stacks Tag `06LJ`.  Once the maximal-adic completion
of the strict local colimit is known to be Noetherian and flat over the colimit, faithful-flat
descent proves that the colimit itself is Noetherian.
-/

open Module
open scoped TensorProduct

universe u v

namespace Pcf.Stacks

/-- A flat module over a local ring with nilpotent maximal ideal is free.  This is the
infinite-rank form of Stacks Tag `051F`; the chosen lifts of a residue-field basis span because
iterating Nakayama's relation terminates at a power of the maximal ideal. -/
theorem flatModule_free_of_isNilpotent_maximalIdeal
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    [IsLocalRing A] [Module.Flat A M]
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal A)) : Module.Free A M := by
  let k := IsLocalRing.ResidueField A
  let w := Module.Free.chooseBasis k (k ⊗[A] M)
  obtain ⟨basisLift, hbasisLift⟩ :=
    (TensorProduct.mk_surjective A M k Quotient.mk_surjective).comp_left w
  let f := TensorProduct.mk A k M 1
  have hli : LinearIndependent k (f ∘ basisLift) := by
    rw [show f ∘ basisLift = w from hbasisLift]
    exact w.linearIndependent
  have hliA : LinearIndependent A basisLift := by
    apply IsLocalRing.linearIndependent_of_flat
    simpa [k, f] using hli
  apply Module.Free.of_basis
  apply Basis.mk hliA
  let N := Submodule.span A (Set.range basisLift)
  have hmap : N.map f = ⊤ := by
    change (Submodule.span A (Set.range basisLift)).map f = ⊤
    rw [Submodule.map_span, ← Submodule.restrictScalars_span A k
      Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
      ← w.span_eq, ← Set.range_comp, show f ∘ basisLift = w from hbasisLift]
  have hsup : N ⊔ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) = ⊤ := by
    have hcomap := congrArg (Submodule.comap f) hmap
    rw [Submodule.comap_map_eq, Submodule.comap_top] at hcomap
    have hker : f.ker = IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
      exact LinearMap.ker_tensorProductMk
        (R := A) (Q := M) (I := IsLocalRing.maximalIdeal A)
    rw [hker] at hcomap
    exact hcomap
  obtain ⟨n, hn⟩ := hnil
  have hpow : ∀ q : ℕ, (⊤ : Submodule A M) ≤
      N ⊔ (IsLocalRing.maximalIdeal A) ^ q • (⊤ : Submodule A M) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      calc
        (⊤ : Submodule A M) =
            N ⊔ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := hsup.symm
        _ ≤ N ⊔ (IsLocalRing.maximalIdeal A) ^ (q + 1) •
            (⊤ : Submodule A M) := sup_le le_sup_left (by
          calc
            IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≤
                IsLocalRing.maximalIdeal A •
                  (N ⊔ (IsLocalRing.maximalIdeal A) ^ q • (⊤ : Submodule A M)) :=
              Submodule.smul_mono le_rfl ih
            _ = IsLocalRing.maximalIdeal A • N ⊔
                IsLocalRing.maximalIdeal A •
                  ((IsLocalRing.maximalIdeal A) ^ q • (⊤ : Submodule A M)) :=
              Submodule.smul_sup _ _ _
            _ ≤ N ⊔ (IsLocalRing.maximalIdeal A) ^ (q + 1) •
                (⊤ : Submodule A M) := by
              apply sup_le_sup
              · exact (Submodule.smul_le).mpr fun a _ x hx ↦ N.smul_mem a hx
              · rw [← Submodule.mul_smul, ← pow_succ'])
  simpa [N, hn] using hpow n

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
