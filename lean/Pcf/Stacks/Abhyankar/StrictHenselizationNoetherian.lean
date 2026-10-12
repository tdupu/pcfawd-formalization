/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Functoriality
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

universe u v w

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

/-- Over a local ring with nilpotent maximal ideal, lifts of a basis modulo the maximal ideal
form a basis of any flat module.  Unlike `flatModule_free_of_isNilpotent_maximalIdeal`, this
records the chosen basis; that compatibility is needed across all quotient powers in Stacks Tag
`07QM`. -/
theorem exists_basis_of_flat_of_isNilpotent_maximalIdeal
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    [IsLocalRing A] [Module.Flat A M]
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal A))
    {ι : Type w} (v : ι → M)
    (b : Basis ι (IsLocalRing.ResidueField A)
      ((IsLocalRing.ResidueField A) ⊗[A] M))
    (hv : TensorProduct.mk A (IsLocalRing.ResidueField A) M 1 ∘ v = b) :
    ∃ bA : Basis ι A M, ∀ i, bA i = v i := by
  let k := IsLocalRing.ResidueField A
  let f := TensorProduct.mk A k M 1
  have hli : LinearIndependent k (f ∘ v) := by
    rw [show f ∘ v = b from hv]
    exact b.linearIndependent
  have hliA : LinearIndependent A v := by
    apply IsLocalRing.linearIndependent_of_flat
    simpa [k, f] using hli
  let N := Submodule.span A (Set.range v)
  have hmap : N.map f = ⊤ := by
    change (Submodule.span A (Set.range v)).map f = ⊤
    rw [Submodule.map_span, ← Submodule.restrictScalars_span A k
      Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
      ← b.span_eq, ← Set.range_comp, show f ∘ v = b from hv]
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
  have hspan : Submodule.span A (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    simpa [N, hn] using hpow n
  let bA := Basis.mk hliA hspan.ge
  exact ⟨bA, fun i ↦ by simp [bA]⟩

/-- A surjective local ring map induces an isomorphism on residue fields.  We first record the
bijectivity of Mathlib's canonical residue-field map so quotient maps by ideal powers can reuse
the functorial map rather than a hand-built double-quotient equivalence. -/
theorem IsLocalRing.ResidueField.map_bijective_of_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  refine ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨b, rfl⟩ :=
    (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal B)) y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨IsLocalRing.residue A a, by
    rw [IsLocalRing.ResidueField.map_residue]
    rfl⟩

/-- The residue-field equivalence induced by a surjective local ring map. -/
noncomputable def IsLocalRing.ResidueField.mapEquivOfSurjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Surjective f) :
    IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField B :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f)
    (IsLocalRing.ResidueField.map_bijective_of_surjective f hf)

/-- Transport a basis along a semilinear equivalence whose scalar map is a ring equivalence. -/
noncomputable def Module.Basis.mapSemilinear
    {ι : Type u} {A : Type v} {B : Type w}
    [Semiring A] [Semiring B]
    {M : Type*} {N : Type*}
    [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module B N]
    (σ : A ≃+* B)
    [RingHomInvPair (σ : A →+* B) (σ.symm : B →+* A)]
    [RingHomInvPair (σ.symm : B →+* A) (σ : A →+* B)]
    (b : Module.Basis ι A M)
    (e : @LinearEquiv A B _ _ (σ : A →+* B) (σ.symm : B →+* A) _ _ M N _ _ _ _) :
    Module.Basis ι B N :=
  Module.Basis.ofRepr <|
    e.symm.trans <| b.repr.trans <|
      Finsupp.mapRange.linearEquiv σ.toSemilinearEquiv

theorem Module.Basis.mapSemilinear_apply
    {ι : Type u} {A : Type v} {B : Type w}
    [Semiring A] [Semiring B]
    {M : Type*} {N : Type*}
    [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module B N]
    (σ : A ≃+* B)
    [RingHomInvPair (σ : A →+* B) (σ.symm : B →+* A)]
    [RingHomInvPair (σ.symm : B →+* A) (σ : A →+* B)]
    (b : Module.Basis ι A M)
    (e : @LinearEquiv A B _ _ (σ : A →+* B) (σ.symm : B →+* A) _ _ M N _ _ _ _)
    (i : ι) :
    Module.Basis.mapSemilinear σ b e i = e (b i) := by
  apply (Module.Basis.mapSemilinear σ b e).repr.injective
  simp [Module.Basis.mapSemilinear]

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

/-- A linear map that is injective modulo every power of an ideal induces an injective map on
adic completions.  This is the inverse-limit injectivity step needed when a single family is a
basis in every quotient in Stacks Tag `06LJ`. -/
theorem AdicCompletion.map_injective_of_reduceModIdeal
    {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N)
    (h : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Injective (AdicCompletion.map I f) := by
  intro x y hxy
  apply AdicCompletion.ext
  intro n
  apply h n
  simpa only [AdicCompletion.map_val_apply] using congrArg (fun z ↦ z.val n) hxy

/-- A linear map that is bijective modulo every power of an ideal induces a bijection on adic
completions.  Surjectivity already follows from surjectivity modulo the ideal, while injectivity
is checked at every level of the inverse limit. -/
theorem AdicCompletion.map_bijective_of_reduceModIdeal
    {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N)
    (h : ∀ n : ℕ, Function.Bijective (f.reduceModIdeal (I ^ n))) :
    Function.Bijective (AdicCompletion.map I f) := by
  refine ⟨AdicCompletion.map_injective_of_reduceModIdeal I f fun n ↦ (h n).1, ?_⟩
  apply AdicCompletion.map_surjective_of_mkQ_comp_surjective
  have h1 := (h 1).2
  rw [pow_one] at h1
  intro y
  obtain ⟨x, hx⟩ := h1 y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (I • ⊤ : Submodule A M) x
  refine ⟨x, ?_⟩
  change Submodule.Quotient.mk (f x) = y
  exact hx

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
#print axioms exists_basis_of_flat_of_isNilpotent_maximalIdeal
#print axioms IsLocalRing.ResidueField.map_bijective_of_surjective
#print axioms IsLocalRing.ResidueField.mapEquivOfSurjective
#print axioms Module.Basis.mapSemilinear
#print axioms Module.Basis.mapSemilinear_apply
#print axioms AdicCompletion.map_injective_of_reduceModIdeal
#print axioms AdicCompletion.map_bijective_of_reduceModIdeal
#print axioms PointedEtaleNeighborhood.localColimit_quotient_maximalIdeal_pow_free

end Pcf.Stacks
