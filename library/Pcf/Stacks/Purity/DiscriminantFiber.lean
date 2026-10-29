/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The discriminant after base change

This file starts the discriminant branch of the dimension-two argument in Stacks Tag `0BMA`.
Its first input is the basis-level base-change identity used to pass the discriminant to residue
fields and height-one localizations.
-/

@[expose] public section

open scoped TensorProduct

namespace Pcf.Stacks

universe u v w z

/-- In a Noetherian domain, a nonzero element which becomes a unit at every height-one prime is
already a unit.  This is the principal-ideal-theorem step in the discriminant proof of Stacks
Tag `0BJF`. -/
theorem isUnit_of_isUnit_localizationAt_height_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {d : R} (hd : d ≠ 0)
    (hunit : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap R (Localization.AtPrime p) d)) :
    IsUnit d := by
  by_contra hdu
  obtain ⟨p, hp⟩ := (Ideal.span {d}).nonempty_minimalPrimes (by simpa)
  letI : p.IsPrime := hp.isPrime
  have hdp : d ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton d))
  have hp_ne_bot : p ≠ ⊥ := by
    intro hp0
    rw [hp0, Ideal.mem_bot] at hdp
    exact hd hdp
  have hp_height : p.height = 1 := by
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
        (Ideal.span {d}) p hp
    · rw [Order.one_le_iff_ne_zero]
      intro hp0
      exact hp_ne_bot (Ideal.height_eq_zero_iff_eq_bot.mp hp0)
  have hu := hunit p hp_height
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p d] at hu
  exact hu hdp

/-- The trace matrix of a finite free algebra maps to the trace matrix of its base change. -/
theorem Algebra.traceMatrix_baseChange
    {R : Type u} {S : Type v} {A : Type w} {ι : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) :
    Algebra.traceMatrix A (Algebra.TensorProduct.basis A b) =
      (algebraMap R A).mapMatrix (Algebra.traceMatrix R b) := by
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    Algebra.TensorProduct.basis_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change LinearMap.trace A (A ⊗[R] S)
      (Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ[R] (b i * b j))) =
    algebraMap R A (LinearMap.trace R S (Algebra.lmul R S (b i * b j)))
  rw [← LinearMap.trace_baseChange (Algebra.lmul R S (b i * b j)) A,
    Algebra.baseChange_lmul]

/-- Discriminants commute with arbitrary scalar extension for a chosen finite basis. -/
theorem Algebra.discr_baseChange
    {R : Type u} {S : Type v} {A : Type w} {ι : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) :
    Algebra.discr A (Algebra.TensorProduct.basis A b) =
      algebraMap R A (Algebra.discr R b) := by
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det,
    Algebra.traceMatrix_baseChange b]

/-- Nondegeneracy of the trace pairing is invariant under an algebra equivalence. -/
theorem Algebra.traceForm_nondegenerate_of_algEquiv
    {K : Type u} {S : Type v} {T : Type w}
    [CommRing K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (e : S ≃ₐ[K] T) (hT : (Algebra.traceForm K T).Nondegenerate) :
    (Algebra.traceForm K S).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    simpa only [map_zero] using hT.1 (e x) (fun y ↦ by
      rw [Algebra.traceForm_apply, ← e.apply_symm_apply y, ← map_mul,
        Algebra.trace_eq_of_algEquiv]
      exact hx (e.symm y))
  · intro y hy
    apply e.injective
    simpa only [map_zero] using hT.2 (e y) (fun x ↦ by
      rw [Algebra.traceForm_apply, ← e.apply_symm_apply x, ← map_mul,
        Algebra.trace_eq_of_algEquiv]
      exact hy (e.symm x))

/-- The trace pairing on a product is nondegenerate when the two factor pairings are. -/
theorem Algebra.traceForm_prod_nondegenerate
    {K : Type u} {S : Type v} {T : Type w}
    [CommRing K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    [Module.Free K S] [Module.Finite K S]
    [Module.Free K T] [Module.Finite K T]
    (hS : (Algebra.traceForm K S).Nondegenerate)
    (hT : (Algebra.traceForm K T).Nondegenerate) :
    (Algebra.traceForm K (S × T)).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hS.1 x.1
      intro y
      simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
        mul_zero, Algebra.trace_prod_apply, map_zero, add_zero] using hx (y, 0)
    · apply hT.1 x.2
      intro y
      simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
        mul_zero, Algebra.trace_prod_apply, map_zero, zero_add] using hx (0, y)
  · intro y hy
    apply Prod.ext
    · apply hS.2 y.1
      intro x
      simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
        zero_mul, Algebra.trace_prod_apply, map_zero, add_zero] using hy (x, 0)
    · apply hT.2 y.2
      intro x
      simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
        zero_mul, Algebra.trace_prod_apply, map_zero, zero_add] using hy (0, x)

/-- A finite product of finite algebras with nondegenerate trace pairings again has a
nondegenerate trace pairing. -/
theorem Algebra.traceForm_pi_nondegenerate
    (K : Type u) [Field K]
    (I : Type v) [Finite I]
    (A : I → Type w)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, Module.Free K (A i)] [∀ i, Module.Finite K (A i)]
    (hA : ∀ i, (Algebra.traceForm K (A i)).Nondegenerate) :
    (Algebra.traceForm K (∀ i, A i)).Nondegenerate := by
  classical
  let P : Type v → Prop := fun J ↦
    ∀ (B : J → Type w)
      [∀ j, CommRing (B j)] [∀ j, Algebra K (B j)]
      [∀ j, Module.Free K (B j)] [∀ j, Module.Finite K (B j)],
      (∀ j, (Algebra.traceForm K (B j)).Nondegenerate) →
        (Algebra.traceForm K (∀ j, B j)).Nondegenerate
  apply Finite.induction_empty_option (P := P)
      (fun {J J'} e hJ B _ _ _ _ hB ↦ ?_)
      (fun B _ _ _ _ _ ↦ ?_)
      (fun {J} _ hJ B _ _ _ _ hB ↦ ?_)
      I A hA
  · let ePi : (∀ j : J, B (e j)) ≃ₐ[K] (∀ j : J', B j) :=
      AlgEquiv.piCongrLeft K B e
    exact Algebra.traceForm_nondegenerate_of_algEquiv ePi.symm
      (hJ (fun j ↦ B (e j)) (fun j ↦ hB (e j)))
  · constructor <;> intro x hx <;> exact Subsingleton.elim x 0
  · let ePi : (∀ j : Option J, B j) ≃ₐ[K]
        B none × (∀ j : J, B (some j)) :=
      { __ := RingEquiv.piOptionEquivProd
        commutes' := fun _ ↦ rfl }
    exact Algebra.traceForm_nondegenerate_of_algEquiv ePi
      (Algebra.traceForm_prod_nondegenerate (hB none)
        (hJ (fun j ↦ B (some j)) (fun j ↦ hB (some j))))

/-- A finite formally-etale algebra over a field has nondegenerate trace pairing. -/
theorem Algebra.traceForm_nondegenerate_of_formallyEtale
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    [Algebra.EssFiniteType K T] [Algebra.FormallyEtale K T]
    [Module.Free K T] [Module.Finite K T] :
    (Algebra.traceForm K T).Nondegenerate := by
  classical
  obtain ⟨I, _, Ai, _, _, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K T).mp inferInstance
  letI : Fintype I := Fintype.ofFinite I
  letI : Module.Finite K (∀ i, Ai i) := Module.Finite.equiv e.toLinearEquiv
  letI (i : I) : Module.Finite K (Ai i) :=
    Module.Finite.of_surjective (LinearMap.proj i) (by
      intro x
      exact ⟨Pi.single i x, by simp⟩)
  have hPi : (Algebra.traceForm K (∀ i, Ai i)).Nondegenerate :=
    Algebra.traceForm_pi_nondegenerate K I Ai
      (fun i ↦ traceForm_nondegenerate K (Ai i))
  exact Algebra.traceForm_nondegenerate_of_algEquiv e hPi

/-- The discriminant of a basis of a finite formally-etale algebra over a field is nonzero. -/
theorem Algebra.discr_ne_zero_of_formallyEtale_of_basis
    {K T : Type u} {ι : Type z}
    [Field K] [CommRing T] [Algebra K T]
    [Algebra.EssFiniteType K T] [Algebra.FormallyEtale K T]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K T) : Algebra.discr K b ≠ 0 := by
  letI : Module.Free K T := Module.Free.of_basis b
  letI : Module.Finite K T := Module.Finite.of_basis b
  have hnondeg := Algebra.traceForm_nondegenerate_of_formallyEtale (K := K) (T := T)
  simpa only [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def] using
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnondeg

/-- Generic formal etaleness makes the discriminant of a finite free algebra nonzero. -/
theorem Algebra.discr_ne_zero_of_genericFiber_formallyEtale
    {R S K : Type u} {ι : Type z}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S)
    [Algebra.FormallyEtale K (K ⊗[R] S)] :
    Algebra.discr R b ≠ 0 := by
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  let bK : Module.Basis ι K (K ⊗[R] S) := Algebra.TensorProduct.basis K b
  have hK : Algebra.discr K bK ≠ 0 :=
    Algebra.discr_ne_zero_of_formallyEtale_of_basis bK
  change Algebra.discr K (Algebra.TensorProduct.basis K b) ≠ 0 at hK
  rw [Algebra.discr_baseChange] at hK
  intro h
  apply hK
  rw [h, map_zero]

/-- The discriminant of a basis of an etale algebra over a local ring is a unit. -/
theorem Algebra.isUnit_discr_of_etale_of_basis
    {R S : Type u} {ι : Type z}
    [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) :
    IsUnit (Algebra.discr R b) := by
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  let K := IsLocalRing.ResidueField R
  let bK : Module.Basis ι K (K ⊗[R] S) := Algebra.TensorProduct.basis K b
  have hK : Algebra.discr K bK ≠ 0 :=
    Algebra.discr_ne_zero_of_formallyEtale_of_basis bK
  change Algebra.discr K (Algebra.TensorProduct.basis K b) ≠ 0 at hK
  rw [Algebra.discr_baseChange] at hK
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (Algebra.discr R b)).mp (by
    simpa [K, IsLocalRing.ResidueField.algebraMap_eq] using hK)

/-- Etaleness after localization at a prime makes the localized discriminant a unit. -/
theorem Algebra.isUnit_map_discr_of_etale_baseChange
    {R S : Type u} {ι : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (p : Ideal R) [p.IsPrime]
    [Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] S)] :
    IsUnit (algebraMap R (Localization.AtPrime p) (Algebra.discr R b)) := by
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  let bp : Module.Basis ι (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] S) :=
    Algebra.TensorProduct.basis (Localization.AtPrime p) b
  have hp := Algebra.isUnit_discr_of_etale_of_basis bp
  change IsUnit (Algebra.discr (Localization.AtPrime p)
    (Algebra.TensorProduct.basis (Localization.AtPrime p) b)) at hp
  rwa [Algebra.discr_baseChange] at hp

/-- A finite free algebra over a field with nonzero discriminant is reduced.  The proof is the
trace-pairing argument used in the local form of Stacks Tag `0BJF`: a nilpotent element pairs to
zero with every element, hence vanishes by nondegeneracy. -/
theorem Algebra.isReduced_of_discr_ne_zero_of_basis
    {K : Type u} {T : Type v} {ι : Type z}
    [Field K] [CommRing T] [Algebra K T] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K T) (hdisc : Algebra.discr K b ≠ 0) :
    IsReduced T := by
  letI : Module.Free K T := Module.Free.of_basis b
  letI : Module.Finite K T := Module.Finite.of_basis b
  have hnondeg : (Algebra.traceForm K T).Nondegenerate :=
    (Algebra.traceForm K T).nondegenerate_of_det_ne_zero b (by
      simpa only [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def] using hdisc)
  constructor
  intro x hx
  apply hnondeg.1 x
  intro y
  rw [Algebra.traceForm_apply]
  exact (Algebra.isNilpotent_trace_of_isNilpotent
    ((Commute.all x y).isNilpotent_mul_right hx)).eq_zero

/-- A finite free local algebra over a field with nonzero discriminant is a finite separable
field extension. -/
theorem Algebra.isSeparable_of_isLocalRing_of_discr_ne_zero_of_basis
    {K : Type u} {T : Type v} {ι : Type z}
    [Field K] [CommRing T] [Algebra K T] [IsLocalRing T]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K T) (hdisc : Algebra.discr K b ≠ 0) :
    Algebra.IsSeparable K T := by
  letI : Module.Free K T := Module.Free.of_basis b
  letI : Module.Finite K T := Module.Finite.of_basis b
  letI : IsReduced T := Algebra.isReduced_of_discr_ne_zero_of_basis b hdisc
  letI : IsArtinianRing T := isArtinian_of_tower K inferInstance
  letI : Field T := (IsArtinianRing.isField_of_isReduced_of_isLocalRing T).toField
  have hnondeg : (Algebra.traceForm K T).Nondegenerate :=
    (Algebra.traceForm K T).nondegenerate_of_det_ne_zero b (by
      simpa only [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def] using hdisc)
  exact ((traceForm_nondegenerate_tfae K T).out 3 1).mp hnondeg

/-- A finite free local algebra over a field with nonzero discriminant is a field. -/
theorem Algebra.isField_of_isLocalRing_of_discr_ne_zero_of_basis
    {K : Type u} {T : Type v} {ι : Type z}
    [Field K] [CommRing T] [Algebra K T] [IsLocalRing T]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K T) (hdisc : Algebra.discr K b ≠ 0) :
    IsField T := by
  letI : Module.Finite K T := Module.Finite.of_basis b
  letI : IsReduced T := Algebra.isReduced_of_discr_ne_zero_of_basis b hdisc
  letI : IsArtinianRing T := isArtinian_of_tower K inferInstance
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing T

/-- The local finite-free field-fibre form of the discriminant criterion. -/
theorem Algebra.formallyEtale_of_isLocalRing_of_discr_ne_zero_of_basis
    {K : Type u} {T : Type v} {ι : Type z}
    [Field K] [CommRing T] [Algebra K T] [IsLocalRing T]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K T) (hdisc : Algebra.discr K b ≠ 0) :
    Algebra.FormallyEtale K T := by
  letI : Module.Free K T := Module.Free.of_basis b
  letI : Module.Finite K T := Module.Finite.of_basis b
  letI : IsReduced T := Algebra.isReduced_of_discr_ne_zero_of_basis b hdisc
  letI : IsArtinianRing T := isArtinian_of_tower K inferInstance
  letI : Field T := (IsArtinianRing.isField_of_isReduced_of_isLocalRing T).toField
  letI : Algebra.IsSeparable K T :=
    Algebra.isSeparable_of_isLocalRing_of_discr_ne_zero_of_basis b hdisc
  exact Algebra.FormallyEtale.of_isSeparable K T

/-- The local discriminant criterion used in the dimension-two branch of Tag `0BMA`.  If a
finite free local algebra has unit discriminant, its residue fibre is a separable field; hence
the original local homomorphism is formally unramified. -/
theorem Algebra.formallyUnramified_of_isUnit_discr_of_basis
    {R : Type u} {S : Type v} {ι : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    Algebra.FormallyUnramified R S := by
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  let bT : Module.Basis ι (IsLocalRing.ResidueField R)
      ((IsLocalRing.ResidueField R) ⊗[R] S) :=
    Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b
  have hdiscT : Algebra.discr (IsLocalRing.ResidueField R) bT ≠ 0 := by
    change Algebra.discr (IsLocalRing.ResidueField R)
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b) ≠ 0
    rw [Algebra.discr_baseChange]
    simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
      (IsLocalRing.residue_ne_zero_iff_isUnit (Algebra.discr R b)).mpr hdisc
  have hTfield : IsField ((IsLocalRing.ResidueField R) ⊗[R] S) :=
    Algebra.isField_of_isLocalRing_of_discr_ne_zero_of_basis bT hdiscT
  letI : Field ((IsLocalRing.ResidueField R) ⊗[R] S) := hTfield.toField
  letI : Algebra (IsLocalRing.ResidueField R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    (inferInstanceAs <|
      Algebra (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))
  haveI : IsScalarTower R (IsLocalRing.ResidueField R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    (inferInstanceAs <|
      IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))
  let eQuot :
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) ≃ₐ[IsLocalRing.ResidueField R]
        ((IsLocalRing.ResidueField R) ⊗[R] S) :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (IsLocalRing.maximalIdeal R)
  have hquotField :
      IsField (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    eQuot.toMulEquiv.isField hTfield
  have hmap :
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
        IsLocalRing.maximalIdeal S := by
    apply IsLocalRing.eq_maximalIdeal
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact hquotField
  let eResidue :
      IsLocalRing.ResidueField S ≃ₐ[IsLocalRing.ResidueField R]
        ((IsLocalRing.ResidueField R) ⊗[R] S) :=
    { __ := (Ideal.quotEquivOfEq hmap.symm).trans eQuot.toRingEquiv
      commutes' := by
        intro y
        obtain ⟨x, rfl⟩ :=
          (IsLocalRing.residue_surjective (R := R)) y
        change eQuot (Ideal.quotEquivOfEq hmap.symm
          (Ideal.Quotient.mk _ (algebraMap R S x))) =
            algebraMap R (IsLocalRing.ResidueField R) x ⊗ₜ[R] (1 : S)
        rw [Ideal.quotEquivOfEq_mk]
        change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S
          (IsLocalRing.maximalIdeal R))
            (Ideal.Quotient.mk _ (algebraMap R S x)) = _
        rw [
          Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul x).symm }
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      ((IsLocalRing.ResidueField R) ⊗[R] S) :=
    Algebra.isSeparable_of_isLocalRing_of_discr_ne_zero_of_basis bT hdiscT
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) :=
    Algebra.IsSeparable.of_algHom (IsLocalRing.ResidueField R)
      ((IsLocalRing.ResidueField R) ⊗[R] S) eResidue.toAlgHom
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmap

/-- A finite-presentation flat local map with unit discriminant is etale. -/
theorem Algebra.etale_of_isUnit_discr_of_basis
    {R : Type u} {S : Type v} {ι : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    Algebra.Etale R S := by
  letI : Algebra.FormallyUnramified R S :=
    Algebra.formallyUnramified_of_isUnit_discr_of_basis b hdisc
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- The local finite-free `0BJF` endpoint, with the height-one discriminant test exposed. -/
theorem Algebra.etale_of_discr_ne_zero_of_isUnit_at_height_one
    {R : Type u} {S : Type v} {ι : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (hdisc : Algebra.discr R b ≠ 0)
    (hheightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap R (Localization.AtPrime p) (Algebra.discr R b))) :
    Algebra.Etale R S := by
  apply Algebra.etale_of_isUnit_discr_of_basis b
  exact isUnit_of_isUnit_localizationAt_height_one hdisc hheightOne

/-- The finite-free local discriminant endpoint with the generic condition stated geometrically:
the generic fibre is formally etale and the discriminant is a unit at every height-one point. -/
theorem Algebra.etale_of_genericFiber_formallyEtale_of_isUnit_at_height_one
    {R S K : Type u} {ι : Type z}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S)
    [Algebra.FormallyEtale K (K ⊗[R] S)]
    (hheightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap R (Localization.AtPrime p) (Algebra.discr R b))) :
    Algebra.Etale R S := by
  apply Algebra.etale_of_discr_ne_zero_of_isUnit_at_height_one b
  · exact Algebra.discr_ne_zero_of_genericFiber_formallyEtale (K := K) b
  · exact hheightOne

/-- The finite-free local `0BJF` criterion in geometric form: the generic fibre and every
height-one base change are etale, so the original local algebra is etale. -/
theorem Algebra.etale_of_genericFiber_and_heightOne_baseChange
    {R S K : Type u} {ι : Type z}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S)
    [Algebra.FormallyEtale K (K ⊗[R] S)]
    (hheightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Algebra.Etale (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[R] S)) :
    Algebra.Etale R S := by
  apply Algebra.etale_of_genericFiber_formallyEtale_of_isUnit_at_height_one (K := K) b
  intro p _ hp
  letI : Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] S) := hheightOne p hp
  exact Algebra.isUnit_map_discr_of_etale_baseChange b p

end Pcf.Stacks
