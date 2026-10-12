/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Flat.EquationalCriterion
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

/-- Arbitrary products of flat modules over a Noetherian ring are flat.  This is the
product-flatness input in the proof of Stacks Tag `06LE`. -/
theorem Module.Flat.pi_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {ι : Type v} (M : ι → Type w)
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)]
    [∀ t, Module.Flat R (M t)] :
    Module.Flat R (∀ t, M t) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x h
  let φ := Fintype.linearCombination R f
  have hker : φ.ker.FG := by
    apply Submodule.FG.of_le (T := ⊤) Module.Finite.fg_top
    exact le_top
  obtain ⟨k, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hker
  have hrel (t : ι) : ∑ i, f i • x i t = 0 := by
    simpa [Pi.smul_apply] using congrFun h t
  choose kt a y hxy ha using fun t ↦
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (hrel t)
  have hacol (t : ι) (j : Fin (kt t)) :
      (fun i ↦ a t i j) ∈ φ.ker := by
    rw [LinearMap.mem_ker]
    simpa [φ, Fintype.linearCombination_apply, mul_comm] using ha t j
  choose c hc using fun t (j : Fin (kt t)) ↦
    (Submodule.mem_span_range_iff_exists_fun R).mp (hg ▸ hacol t j)
  refine ⟨k, (fun i s ↦ g s i),
    (fun s t ↦ ∑ j, c t j s • y t j), ?_, ?_⟩
  · intro i
    funext t
    simp only [Pi.smul_apply, Finset.sum_apply]
    calc
      x i t = ∑ j, a t i j • y t j := hxy t i
      _ = ∑ j, (∑ s, c t j s * g s i) • y t j := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        simpa [Pi.smul_apply, mul_comm] using
          (congrArg (fun q : Fin l → R ↦ q i) (hc t j)).symm
      _ = ∑ j, ∑ s, (c t j s * g s i) • y t j := by
        simp_rw [Finset.sum_smul]
      _ = ∑ s, ∑ j, (g s i * c t j s) • y t j := by
        rw [Finset.sum_comm]
        simp only [mul_comm]
      _ = ∑ s, g s i • ∑ j, c t j s • y t j := by
        simp_rw [Finset.smul_sum, mul_smul]
  · intro s
    have hgs : g s ∈ φ.ker := by
      rw [← hg]
      exact Submodule.subset_span (Set.mem_range_self s)
    simpa [φ, Fintype.linearCombination_apply, mul_comm] using
      (show φ (g s) = 0 from LinearMap.mem_ker.mp hgs)

/-- Arbitrary products of the base ring are flat when the base is Noetherian. -/
theorem flat_pi_self_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type v) :
    Module.Flat R (ι → R) :=
  Module.Flat.pi_of_isNoetherianRing R (fun _ : ι ↦ R)

/-- Products of completed coefficient modules are flat over the original Noetherian ring. -/
theorem AdicCompletion.pi_flat_of_isNoetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (ι : Type v) :
    Module.Flat R (ι → AdicCompletion I R) :=
  Module.Flat.pi_of_isNoetherianRing R (fun _ : ι ↦ AdicCompletion I R)

/-- A module admitting a tensor-injective map to a flat module is flat.  Applied to the
completion-to-product map, this isolates the universal-injectivity input in Stacks Tag `06LE`. -/
theorem Module.Flat.of_forall_ideal_lTensor_injective
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (h : ∀ I : Ideal R, Function.Injective (f.lTensor I)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply (injective_iff_map_eq_zero _).mp (h I)
  apply (injective_iff_map_eq_zero _).mp
    (Module.Flat.iff_rTensor_injective'.mp (inferInstance : Module.Flat R N) I)
  calc
    I.subtype.rTensor N (f.lTensor I x) =
        TensorProduct.map I.subtype f x := by
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
    _ = f.lTensor R (I.subtype.rTensor M x) := by
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]
    _ = 0 := by rw [hx, map_zero]

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

/-- If a local algebra identifies the extended maximal ideal with the target's maximal ideal,
its closed fiber is canonically the target residue field. -/
noncomputable def residueTensorEquivOfMapMaximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    (IsLocalRing.ResidueField A ⊗[A] B) ≃ₗ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField B := by
  let eRing := Ideal.quotEquivOfEq hmax
  letI : Algebra (IsLocalRing.ResidueField A)
      (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap])
  letI : Module (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.instModule
  let eRing' :
      (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ≃+*
        IsLocalRing.ResidueField B := eRing
  let eLin :
      (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ≃ₗ[
        IsLocalRing.ResidueField A] IsLocalRing.ResidueField B :=
    eRing'.toAddEquiv.toLinearEquiv (by
      rintro ⟨a⟩ ⟨b⟩
      rfl)
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
    (IsLocalRing.maximalIdeal A)).symm.toLinearEquiv ≪≫ₗ eLin

@[simp]
theorem residueTensorEquivOfMapMaximalIdeal_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) (b : B) :
    residueTensorEquivOfMapMaximalIdeal hmax (1 ⊗ₜ b) =
      IsLocalRing.residue B b := by
  change Ideal.quotEquivOfEq hmax
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (IsLocalRing.maximalIdeal A)).symm (1 ⊗ₜ b)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    AlgEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]

/-- Reduction of a free module modulo an ideal is the free module over the quotient ring. -/
noncomputable def Finsupp.quotientSMulTopEquiv
    {R : Type u} [CommRing R] (I : Ideal R) (ι : Type v) :
    ((ι →₀ R) ⧸ (I • ⊤ : Submodule R (ι →₀ R))) ≃ₗ[R ⧸ I] ι →₀ (R ⧸ I) := by
  classical
  exact (TensorProduct.quotTensorEquivQuotSMul (ι →₀ R) I).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective ≪≫ₗ
    TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) ι

@[simp]
theorem Finsupp.quotientSMulTopEquiv_mk
    {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} (x : ι →₀ R) :
    Finsupp.quotientSMulTopEquiv I ι (Submodule.Quotient.mk x) =
      Finsupp.mapRange (Ideal.Quotient.mk I) (map_zero _) x := by
  classical
  ext i
  change (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) ι
    ((TensorProduct.quotTensorEquivQuotSMul (ι →₀ R) I).symm
      (Submodule.Quotient.mk x))) i = Ideal.Quotient.mk I (x i)
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    TensorProduct.finsuppScalarRight_apply_tmul_apply, Algebra.smul_def, mul_one,
    Ideal.Quotient.algebraMap_eq]

/-- The canonical map from the completion of a free module to the product of the completed
coefficient modules. -/
noncomputable def AdicCompletion.finsuppToPi
    {R : Type u} [CommRing R] (I : Ideal R) (ι : Type v) :
    AdicCompletion I (ι →₀ R) →ₗ[AdicCompletion I R]
      (ι → AdicCompletion I R) :=
  LinearMap.pi fun i ↦ AdicCompletion.map I (Finsupp.lapply i)

@[simp]
theorem AdicCompletion.finsuppToPi_apply
    {R : Type u} [CommRing R] (I : Ideal R) (ι : Type v)
    (x : AdicCompletion I (ι →₀ R)) (i : ι) :
    AdicCompletion.finsuppToPi I ι x i =
      AdicCompletion.map I (Finsupp.lapply i) x :=
  rfl

/-- The completion-to-product map, viewed over the original ring. -/
noncomputable def AdicCompletion.finsuppToPiRestrictScalars
    {R : Type u} [CommRing R] (I : Ideal R) (ι : Type v) :
    AdicCompletion I (ι →₀ R) →ₗ[R] (ι → AdicCompletion I R) :=
  (AdicCompletion.finsuppToPi I ι).restrictScalars R

/-- The completion of a free module embeds in the product of the completed coefficients. -/
theorem AdicCompletion.finsuppToPi_injective
    {R : Type u} [CommRing R] (I : Ideal R) (ι : Type v) :
    Function.Injective (AdicCompletion.finsuppToPi I ι) := by
  intro x y hxy
  apply AdicCompletion.ext
  intro n
  let e := Finsupp.quotientSMulTopEquiv (I ^ n) ι
  apply e.injective
  ext i
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • ⊤ : Submodule R (ι →₀ R)) (x.val n)
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • ⊤ : Submodule R (ι →₀ R)) (y.val n)
  have hi := congrArg (fun z : AdicCompletion I R ↦ z.val n)
    (congrFun hxy i)
  simp only [AdicCompletion.finsuppToPi_apply,
    AdicCompletion.map_val_apply] at hi
  rw [← ha, ← hb, LinearMap.reduceModIdeal_apply,
    LinearMap.reduceModIdeal_apply] at hi
  have htop : (I ^ n • ⊤ : Submodule R R) = (I ^ n : Ideal R) := by
    simp
  rw [htop] at hi
  rw [← ha, ← hb, Finsupp.quotientSMulTopEquiv_mk,
    Finsupp.quotientSMulTopEquiv_mk]
  simpa [Finsupp.mapRange_apply, Finsupp.lapply_apply,
    Ideal.Quotient.mk_eq_mk] using hi

/-- Flatness of the completed free module is reduced to tensor-injectivity of its canonical
product embedding. -/
theorem AdicCompletion.finsupp_flat_of_forall_ideal_lTensor_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (ι : Type v)
    (h : ∀ J : Ideal R, Function.Injective
      (LinearMap.lTensor (R := R) (↥J)
        (AdicCompletion.finsuppToPiRestrictScalars I ι))) :
    Module.Flat R (AdicCompletion I (ι →₀ R)) := by
  let _ : Module.Flat R (ι → AdicCompletion I R) :=
    AdicCompletion.pi_flat_of_isNoetherian I ι
  exact Module.Flat.of_forall_ideal_lTensor_injective
    (AdicCompletion.finsuppToPiRestrictScalars I ι) h

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

/-- Quotienting the strict local colimit by a base maximal-ideal power as an `R`-module agrees
with quotienting it by the corresponding power of its own maximal ideal as a ring. -/
noncomputable def localColimitQuotientSMulTopEquiv (n : ℕ) :
    (LocalColimit R Ω ⧸
      (IsLocalRing.maximalIdeal R ^ n • ⊤ : Submodule R (LocalColimit R Ω))) ≃ₗ[
        R ⧸ IsLocalRing.maximalIdeal R ^ n]
      LocalColimit R Ω ⧸ IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n := by
  let I := IsLocalRing.maximalIdeal R ^ n
  let J := IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n
  have h : I.map (algebraMap R (LocalColimit R Ω)) = J := by
    dsimp [I, J]
    rw [Ideal.map_pow, map_maximalIdeal_localColimit (R := R) (Ω := Ω)]
  let eQuot :
      (LocalColimit R Ω ⧸ I.map (algebraMap R (LocalColimit R Ω))) ≃ₗ[R ⧸ I]
        LocalColimit R Ω ⧸ J :=
    { __ := (Ideal.quotEquivOfEq h).toAddEquiv
      map_smul' := by
        rintro ⟨r⟩ ⟨s⟩
        rfl }
  exact (TensorProduct.quotTensorEquivQuotSMul
      (LocalColimit R Ω) I).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective ≪≫ₗ
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
      (LocalColimit R Ω) I).symm.toLinearEquiv ≪≫ₗ
    eQuot

omit [IsNoetherianRing R] in
@[simp]
theorem localColimitQuotientSMulTopEquiv_mk (n : ℕ) (s : LocalColimit R Ω) :
    localColimitQuotientSMulTopEquiv (R := R) (Ω := Ω) n
      (Submodule.Quotient.mk s) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n) s := by
  let I := IsLocalRing.maximalIdeal R ^ n
  let J := IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n
  have h : I.map (algebraMap R (LocalColimit R Ω)) = J := by
    dsimp [I, J]
    rw [Ideal.map_pow, map_maximalIdeal_localColimit (R := R) (Ω := Ω)]
  change Ideal.quotEquivOfEq h
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor (LocalColimit R Ω) I).symm
      ((TensorProduct.quotTensorEquivQuotSMul (LocalColimit R Ω) I).symm
        (Submodule.Quotient.mk s))) = Ideal.Quotient.mk J s
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    ← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    AlgEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]

omit [IsNoetherianRing R] in
/-- A single family of lifts of a residue-field basis is a basis modulo every positive power
of the maximal ideal.  This is the compatible-basis step in Stacks Tag `07QM`. -/
theorem exists_localColimit_basis_quotient_maximalIdeal_powers :
    ∃ v : Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (LocalColimit R Ω)) → LocalColimit R Ω,
      ∀ n : ℕ, n ≠ 0 →
        ∃ b : Basis (Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField (LocalColimit R Ω)))
          (R ⧸ IsLocalRing.maximalIdeal R ^ n)
          (LocalColimit R Ω ⧸ IsLocalRing.maximalIdeal (LocalColimit R Ω) ^ n),
          ∀ i, b i = Ideal.Quotient.mk _ (v i) := by
  let C := LocalColimit R Ω
  let ι := Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField C)
  let b₀ := Module.Free.chooseBasis (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField C)
  choose v hv using fun i ↦ IsLocalRing.residue_surjective (b₀ i)
  refine ⟨v, ?_⟩
  intro n hn
  let I := IsLocalRing.maximalIdeal R ^ n
  let J := IsLocalRing.maximalIdeal C ^ n
  have hIle : I ≤ IsLocalRing.maximalIdeal R := Ideal.pow_le_self hn
  have hJle : J ≤ IsLocalRing.maximalIdeal C := Ideal.pow_le_self hn
  have hIne : I ≠ ⊤ := fun h ↦
    (inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal).ne_top
      (eq_top_iff.mpr (h ▸ hIle))
  have hJne : J ≠ ⊤ := fun h ↦
    (inferInstance : (IsLocalRing.maximalIdeal C).IsMaximal).ne_top
      (eq_top_iff.mpr (h ▸ hJle))
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let _ : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (C ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hpow : I.map (algebraMap R C) = J := by
    dsimp [I, J]
    rw [Ideal.map_pow, map_maximalIdeal_localColimit (R := R) (Ω := Ω)]
  let qA : R →+* R ⧸ I := Ideal.Quotient.mk I
  let qB : C →+* C ⧸ J := Ideal.Quotient.mk J
  have hmaxA : (IsLocalRing.maximalIdeal R).map qA =
      IsLocalRing.maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective qA Ideal.Quotient.mk_surjective
  have hmaxB : (IsLocalRing.maximalIdeal C).map qB =
      IsLocalRing.maximalIdeal (C ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective qB Ideal.Quotient.mk_surjective
  have hcomp : (algebraMap (R ⧸ I) (C ⧸ J)).comp qA =
      qB.comp (algebraMap R C) := by
    ext a
    rfl
  have hmaxQ : (IsLocalRing.maximalIdeal (R ⧸ I)).map
      (algebraMap (R ⧸ I) (C ⧸ J)) =
      IsLocalRing.maximalIdeal (C ⧸ J) := by
    rw [← hmaxA, ← hmaxB, Ideal.map_map, hcomp, ← Ideal.map_map,
      map_maximalIdeal_localColimit (R := R) (Ω := Ω)]
  let _ : IsLocalHom (algebraMap (R ⧸ I) (C ⧸ J)) :=
    ((IsLocalRing.local_hom_TFAE _).out 3 1).mp hmaxQ.le
  let _ : IsLocalHom qA := IsLocalHom.of_surjective qA Ideal.Quotient.mk_surjective
  let _ : IsLocalHom qB := IsLocalHom.of_surjective qB Ideal.Quotient.mk_surjective
  let eA := IsLocalRing.ResidueField.mapEquivOfSurjective qA
    Ideal.Quotient.mk_surjective
  let eB := IsLocalRing.ResidueField.mapEquivOfSurjective qB
    Ideal.Quotient.mk_surjective
  let _ : RingHomInvPair
      (eA : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField (R ⧸ I)) eA.symm :=
    RingHomInvPair.of_ringEquiv eA
  let _ : RingHomInvPair
      (eA.symm : IsLocalRing.ResidueField (R ⧸ I) →+* IsLocalRing.ResidueField R) eA :=
    RingHomInvPair.of_ringEquiv_symm eA
  let eResid :
      @LinearEquiv (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (R ⧸ I)) _ _
        (eA : IsLocalRing.ResidueField R →+*
          IsLocalRing.ResidueField (R ⧸ I))
        (eA.symm : IsLocalRing.ResidueField (R ⧸ I) →+*
          IsLocalRing.ResidueField R) _ _
        (IsLocalRing.ResidueField C)
        (IsLocalRing.ResidueField (C ⧸ J)) _ _ _ _ :=
    { __ := eB.toAddEquiv
      map_smul' := by
        intro a x
        rw [Algebra.smul_def, Algebra.smul_def]
        change eB (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField C) a * x) =
          algebraMap (IsLocalRing.ResidueField (R ⧸ I))
            (IsLocalRing.ResidueField (C ⧸ J)) (eA a) * eB x
        rw [map_mul]
        congr 1
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
        rfl }
  let bResid := Module.Basis.mapSemilinear eA b₀ eResid
  have hbResid (i : ι) : bResid i =
      IsLocalRing.residue (C ⧸ J) (Ideal.Quotient.mk J (v i)) := by
    rw [Module.Basis.mapSemilinear_apply]
    change eB (b₀ i) = _
    rw [← hv]
    rfl
  let eFiber := residueTensorEquivOfMapMaximalIdeal hmaxQ
  let bTensor := bResid.map eFiber.symm
  have hbTensor (i : ι) : bTensor i =
      1 ⊗ₜ Ideal.Quotient.mk J (v i) := by
    apply eFiber.injective
    rw [Basis.map_apply, LinearEquiv.apply_symm_apply,
      residueTensorEquivOfMapMaximalIdeal_tmul, hbResid]
  let _ : Module.Flat R C := localColimit_flat (R := R) (Ω := Ω)
  let _ : Module.Flat (R ⧸ I) (C ⧸ I.map (algebraMap R C)) :=
    flat_quotient_map R C I
  let eQuot : (C ⧸ J) ≃ₗ[R ⧸ I] (C ⧸ I.map (algebraMap R C)) :=
    { __ := (Ideal.quotEquivOfEq hpow).symm.toAddEquiv
      map_smul' := by
        rintro ⟨r⟩ ⟨c⟩
        rfl }
  let _ : Module.Flat (R ⧸ I) (C ⧸ J) := Module.Flat.of_linearEquiv eQuot
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (R ⧸ I)) := by
    refine ⟨n, ?_⟩
    rw [← hmaxA, ← Ideal.map_pow]
    change Ideal.map qA I = 0
    exact Ideal.map_quotient_self I
  obtain ⟨b, hb⟩ := exists_basis_of_flat_of_isNilpotent_maximalIdeal hnil
    (fun i : ι ↦ Ideal.Quotient.mk J (v i)) bTensor (by
      funext i
      exact (hbTensor i).symm)
  exact ⟨b, hb⟩

omit [IsNoetherianRing R] in
/-- The compatible lifted residue basis defines a free-module map that is an isomorphism
modulo every maximal-ideal power. -/
theorem exists_localColimit_linearCombination_reduceModIdeal_bijective :
    ∃ v : Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (LocalColimit R Ω)) → LocalColimit R Ω,
      ∀ n : ℕ, Function.Bijective
        ((Finsupp.linearCombination R v).reduceModIdeal
          (IsLocalRing.maximalIdeal R ^ n)) := by
  obtain ⟨v, hv⟩ :=
    exists_localColimit_basis_quotient_maximalIdeal_powers (R := R) (Ω := Ω)
  refine ⟨v, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    let _ : Subsingleton
        ((Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (LocalColimit R Ω)) →₀ R) ⧸
            (IsLocalRing.maximalIdeal R ^ 0 •
              (⊤ : Submodule R
                (Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
                  (IsLocalRing.ResidueField (LocalColimit R Ω)) →₀ R)))) :=
      ⟨fun x y ↦ by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact (Submodule.Quotient.eq _).2 (by
          rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
          exact (show x - y ∈ (⊤ : Submodule R _) from Submodule.mem_top))⟩
    let _ : Subsingleton
        (LocalColimit R Ω ⧸
          (IsLocalRing.maximalIdeal R ^ 0 • ⊤ : Submodule R (LocalColimit R Ω))) :=
      ⟨fun x y ↦ by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact (Submodule.Quotient.eq _).2 (by
          rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
          exact (show x - y ∈ (⊤ : Submodule R _) from Submodule.mem_top))⟩
    exact Function.bijective_of_subsingleton' _
  obtain ⟨b, hb⟩ := hv n hn
  let ι := Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField (LocalColimit R Ω))
  let I := IsLocalRing.maximalIdeal R ^ n
  let eDom := Finsupp.quotientSMulTopEquiv I ι
  let eCod := localColimitQuotientSMulTopEquiv (R := R) (Ω := Ω) n
  let red := (Finsupp.linearCombination R v).reduceModIdeal I
  have hcomm : eCod.toLinearMap.comp red =
      b.repr.symm.toLinearMap.comp eDom.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.reduceModIdeal_apply]
    change localColimitQuotientSMulTopEquiv (R := R) (Ω := Ω) n
      (Submodule.Quotient.mk ((Finsupp.linearCombination R v) x)) =
      b.repr.symm (Finsupp.quotientSMulTopEquiv I ι (Submodule.Quotient.mk x))
    rw [localColimitQuotientSMulTopEquiv_mk, Finsupp.quotientSMulTopEquiv_mk]
    rw [Basis.repr_symm_apply]
    simp only [Finsupp.linearCombination_apply]
    classical
    rw [map_finsuppSum]
    rw [Finsupp.sum_mapRange_index (by simp)]
    apply Finsupp.sum_congr
    intro i _
    rw [hb]
    rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eDom.injective
    apply b.repr.symm.injective
    calc
      b.repr.symm (eDom x) = eCod (red x) := (LinearMap.congr_fun hcomm x).symm
      _ = eCod (red y) := congrArg eCod hxy
      _ = b.repr.symm (eDom y) := LinearMap.congr_fun hcomm y
  · intro y
    refine ⟨eDom.symm (b.repr (eCod y)), ?_⟩
    apply eCod.injective
    calc
      eCod (red (eDom.symm (b.repr (eCod y)))) =
          b.repr.symm (eDom (eDom.symm (b.repr (eCod y)))) :=
        LinearMap.congr_fun hcomm _
      _ = b.repr.symm (b.repr (eCod y)) := by rw [LinearEquiv.apply_symm_apply]
      _ = eCod y := LinearEquiv.symm_apply_apply _ _

omit [IsNoetherianRing R] in
/-- The compatible basis map induces a bijection between the maximal-adic completions of the
free module and the strict local colimit. -/
theorem exists_localColimit_adicCompletion_map_bijective :
    ∃ v : Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (LocalColimit R Ω)) → LocalColimit R Ω,
      Function.Bijective
        (AdicCompletion.map (IsLocalRing.maximalIdeal R)
          (Finsupp.linearCombination R v)) := by
  obtain ⟨v, hv⟩ :=
    exists_localColimit_linearCombination_reduceModIdeal_bijective (R := R) (Ω := Ω)
  exact ⟨v, AdicCompletion.map_bijective_of_reduceModIdeal _ _ hv⟩

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

#print axioms Module.Flat.pi_of_isNoetherianRing
#print axioms flat_pi_self_of_isNoetherianRing
#print axioms AdicCompletion.pi_flat_of_isNoetherian
#print axioms Module.Flat.of_forall_ideal_lTensor_injective
#print axioms flat_quotient_map
#print axioms free_quotient_maximalIdeal_pow_of_flat
#print axioms exists_basis_of_flat_of_isNilpotent_maximalIdeal
#print axioms IsLocalRing.ResidueField.map_bijective_of_surjective
#print axioms IsLocalRing.ResidueField.mapEquivOfSurjective
#print axioms Module.Basis.mapSemilinear
#print axioms Module.Basis.mapSemilinear_apply
#print axioms residueTensorEquivOfMapMaximalIdeal
#print axioms residueTensorEquivOfMapMaximalIdeal_tmul
#print axioms Finsupp.quotientSMulTopEquiv
#print axioms Finsupp.quotientSMulTopEquiv_mk
#print axioms AdicCompletion.finsuppToPi
#print axioms AdicCompletion.finsuppToPi_apply
#print axioms AdicCompletion.finsuppToPiRestrictScalars
#print axioms AdicCompletion.finsuppToPi_injective
#print axioms AdicCompletion.finsupp_flat_of_forall_ideal_lTensor_injective
#print axioms AdicCompletion.map_injective_of_reduceModIdeal
#print axioms AdicCompletion.map_bijective_of_reduceModIdeal
#print axioms PointedEtaleNeighborhood.localColimitQuotientSMulTopEquiv
#print axioms PointedEtaleNeighborhood.localColimitQuotientSMulTopEquiv_mk
#print axioms PointedEtaleNeighborhood.exists_localColimit_basis_quotient_maximalIdeal_powers
#print axioms
  PointedEtaleNeighborhood.exists_localColimit_linearCombination_reduceModIdeal_bijective
#print axioms PointedEtaleNeighborhood.exists_localColimit_adicCompletion_map_bijective
#print axioms PointedEtaleNeighborhood.localColimit_quotient_maximalIdeal_pow_free

end Pcf.Stacks
