/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Quotient
import Pcf.Stacks.Abhyankar.StrictHenselizationDimension

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

/-- Flatness survives simultaneous quotient by an ideal of the base and its extension. -/
theorem flat_quotient_map
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) :
    Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv

/-- If `B` is flat over a local ring `A`, its reduction modulo a positive power of the
maximal ideal is free over the corresponding quotient of `A`.  This is the finite-level
freeness input in Stacks Tag `06LJ`. -/
theorem free_quotient_maximalIdeal_pow_of_flat
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] [Module.Flat A B]
    (n : ℕ) (hn : n ≠ 0) :
    Module.Free (A ⧸ IsLocalRing.maximalIdeal A ^ n)
      (B ⧸ (IsLocalRing.maximalIdeal A ^ n).map (algebraMap A B)) := by
  let I := IsLocalRing.maximalIdeal A ^ n
  have hIle : I ≤ IsLocalRing.maximalIdeal A := by
    exact Ideal.pow_le_self hn
  have hIne : I ≠ ⊤ := by
    intro htop
    apply (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).ne_top
    exact eq_top_iff.mpr (htop ▸ hIle)
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let _ : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let _ : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    flat_quotient_map A B I
  apply flatModule_free_of_isNilpotent_maximalIdeal
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hmax : (IsLocalRing.maximalIdeal A).map q =
      IsLocalRing.maximalIdeal (A ⧸ I) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
  refine ⟨n, ?_⟩
  rw [← hmax, ← Ideal.map_pow]
  change Ideal.map q I = 0
  exact Ideal.map_quotient_self I

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

/-- The canonical quotient-algebra structure at matching maximal-ideal powers. -/
noncomputable instance localColimitQuotientPowAlgebra (n : ℕ) :
    Algebra (R ⧸ IsLocalRing.maximalIdeal R ^ n)
      (LocalColimit R Ω ⧸ IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n) :=
  Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow,
      map_maximalIdeal_localColimit (R := R) (Ω := Ω)])

omit [IsNoetherianRing R] in
/-- Every positive maximal-ideal-power quotient of the strict local colimit is a free module
over the corresponding quotient of the base.  This is the quotient-power comparison and
freeness step used before the inverse-limit argument in Stacks Tag `06LJ`. -/
theorem localColimit_quotient_maximalIdeal_pow_free
    (n : ℕ) (hn : n ≠ 0) :
    Module.Free (R ⧸ IsLocalRing.maximalIdeal R ^ n)
      (LocalColimit R Ω ⧸ IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n) := by
  let _ : Module.Flat R (LocalColimit R Ω) :=
    localColimit_flat (R := R) (Ω := Ω)
  have hfree := free_quotient_maximalIdeal_pow_of_flat R (LocalColimit R Ω) n hn
  have hpow : (IsLocalRing.maximalIdeal R ^ n).map
      (algebraMap R (LocalColimit R Ω)) =
      IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n := by
    rw [Ideal.map_pow, map_maximalIdeal_localColimit (R := R) (Ω := Ω)]
  let e :
      (LocalColimit R Ω ⧸ (IsLocalRing.maximalIdeal R ^ n).map
        (algebraMap R (LocalColimit R Ω))) ≃ₗ[R ⧸ IsLocalRing.maximalIdeal R ^ n]
      (LocalColimit R Ω ⧸ IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n) :=
    { __ := (Ideal.quotEquivOfEq hpow).toAddEquiv
      map_smul' := by
        rintro ⟨r⟩ ⟨a⟩
        rfl }
  exact Module.Free.of_equiv' hfree e

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

#print axioms flat_quotient_map
#print axioms free_quotient_maximalIdeal_pow_of_flat
#print axioms PointedEtaleNeighborhood.localColimit_quotient_maximalIdeal_pow_free

end Pcf.Stacks
