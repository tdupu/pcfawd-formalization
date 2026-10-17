/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Pcf.Stacks.Abhyankar.StrictHenselizationHenselian
public import Pcf.Stacks.Abhyankar.StrictHenselizationRegularity

/-!
# Flatness of the completion of the strict henselization

This file proves part (c) of Stacks Tag `06LJ` for the strict henselization: if `R` is a
Noetherian local ring and `Rˢʰ = LocalColimit R Ω` is the pointed-étale construction of pcf, then
the maximal-adic completion of `Rˢʰ` is flat over `Rˢʰ`.  This discharges the hypothesis `hflat`
of `localColimit_isNoetherianRing_of_completion`, so `Rˢʰ` is Noetherian (the `R ⇒ Rˢʰ`
direction of `06LJ`), its Krull dimension equals that of `R`, and it is regular when `R` is.

The proof follows Stacks:

* For a flat local homomorphism `A → B` of local rings with `A` Noetherian and `𝔪_A B = 𝔪_B`,
  the `𝔪_B`-adic completion of `B` is the `𝔪_A`-adic completion of a free `A`-module (lifts of a
  residue-field basis are a basis modulo every `𝔪_A ^ n`), hence flat over `A` (Tag `06LE`).
  This generalizes pcf's `exists_localColimit_adicCompletion_map_bijective` from `A = R` to an
  arbitrary such `A`.
* Each element of `Rˢʰ` comes from the local ring `L` of a pointed étale stage at its point;
  `L` is Noetherian local, `Rˢʰ` is flat over `L`, and `𝔪_L Rˢʰ = 𝔪_{Rˢʰ}`.  So the completion
  is flat over every such `L`, and flatness over the filtered colimit follows from the equational
  criterion (the "limit argument" of `06LJ`, Algebra Lemma `10.39.6`).

Route note: Stacks uses `R_i ^ sh = R ^ sh` for the stages; we avoid that identification (which
is the separate base-point comparison) by applying the free-completion argument directly to the
flat local map `L → Rˢʰ`.
-/

@[expose] public section

open CategoryTheory Module
open scoped TensorProduct

universe u v w

namespace Pcf.Stacks

section GeneralCompletion

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B]

/-- Reduction of an `A`-algebra modulo `I • ⊤` agrees with reduction modulo the extended ideal,
as a module over `A ⧸ I`. -/
noncomputable def quotientSMulTopEquivQuotientMap (I : Ideal A) :
    (B ⧸ (I • ⊤ : Submodule A B)) ≃ₗ[A ⧸ I] B ⧸ I.map (algebraMap A B) :=
  (TensorProduct.quotTensorEquivQuotSMul B I).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective ≪≫ₗ
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

omit [IsLocalRing A] [IsLocalRing B] in
@[simp]
theorem quotientSMulTopEquivQuotientMap_mk (I : Ideal A) (b : B) :
    quotientSMulTopEquivQuotientMap I (Submodule.Quotient.mk b) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) b := by
  change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm
      ((TensorProduct.quotTensorEquivQuotSMul B I).symm
        (Submodule.Quotient.mk b)) = Ideal.Quotient.mk _ b
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    ← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    AlgEquiv.symm_apply_apply]

variable [Module.Flat A B] [IsLocalHom (algebraMap A B)]
  (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B)

include hmax in
/-- For a flat local algebra with extended maximal ideal, one family of lifts of a residue-field
basis is a basis modulo every positive power of the base maximal ideal.  This is the
compatible-basis step of Stacks Tag `07QM`, for an arbitrary such algebra. -/
theorem exists_basis_quotient_maximalIdeal_powers_of_flat :
    ∃ v : Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) → B,
      ∀ n : ℕ, n ≠ 0 →
        ∃ b : Basis (Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField B))
          (A ⧸ IsLocalRing.maximalIdeal A ^ n)
          (B ⧸ (IsLocalRing.maximalIdeal A ^ n).map (algebraMap A B)),
          ∀ i, b i = Ideal.Quotient.mk _ (v i) := by
  let ι := Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B)
  let b₀ := Module.Free.chooseBasis (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B)
  choose v hv using fun i ↦ IsLocalRing.residue_surjective (b₀ i)
  refine ⟨v, ?_⟩
  intro n hn
  let I := IsLocalRing.maximalIdeal A ^ n
  let J := I.map (algebraMap A B)
  have hIle : I ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self hn
  have hJle : J ≤ IsLocalRing.maximalIdeal B := by
    rw [← hmax]
    exact Ideal.map_mono hIle
  have hIne : I ≠ ⊤ := fun h ↦
    (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).ne_top
      (eq_top_iff.mpr (h ▸ hIle))
  have hJne : J ≠ ⊤ := fun h ↦
    (inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal).ne_top
      (eq_top_iff.mpr (h ▸ hJle))
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let _ : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  let _ : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let qA : A →+* A ⧸ I := Ideal.Quotient.mk I
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  have hmaxA : (IsLocalRing.maximalIdeal A).map qA =
      IsLocalRing.maximalIdeal (A ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective qA Ideal.Quotient.mk_surjective
  have hmaxB : (IsLocalRing.maximalIdeal B).map qB =
      IsLocalRing.maximalIdeal (B ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective qB Ideal.Quotient.mk_surjective
  have hcomp : (algebraMap (A ⧸ I) (B ⧸ J)).comp qA =
      qB.comp (algebraMap A B) := by
    ext a
    rfl
  have hmaxQ : (IsLocalRing.maximalIdeal (A ⧸ I)).map
      (algebraMap (A ⧸ I) (B ⧸ J)) =
      IsLocalRing.maximalIdeal (B ⧸ J) := by
    rw [← hmaxA, ← hmaxB, Ideal.map_map, hcomp, ← Ideal.map_map, hmax]
  let _ : IsLocalHom (algebraMap (A ⧸ I) (B ⧸ J)) :=
    ((IsLocalRing.local_hom_TFAE _).out 3 1).mp hmaxQ.le
  let _ : IsLocalHom qA := IsLocalHom.of_surjective qA Ideal.Quotient.mk_surjective
  let _ : IsLocalHom qB := IsLocalHom.of_surjective qB Ideal.Quotient.mk_surjective
  let eA := IsLocalRing.ResidueField.mapEquivOfSurjective qA
    Ideal.Quotient.mk_surjective
  let eB := IsLocalRing.ResidueField.mapEquivOfSurjective qB
    Ideal.Quotient.mk_surjective
  let _ : RingHomInvPair
      (eA : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField (A ⧸ I)) eA.symm :=
    RingHomInvPair.of_ringEquiv eA
  let _ : RingHomInvPair
      (eA.symm : IsLocalRing.ResidueField (A ⧸ I) →+* IsLocalRing.ResidueField A) eA :=
    RingHomInvPair.of_ringEquiv_symm eA
  let eResid :
      @LinearEquiv (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (A ⧸ I)) _ _
        (eA : IsLocalRing.ResidueField A →+*
          IsLocalRing.ResidueField (A ⧸ I))
        (eA.symm : IsLocalRing.ResidueField (A ⧸ I) →+*
          IsLocalRing.ResidueField A) _ _
        (IsLocalRing.ResidueField B)
        (IsLocalRing.ResidueField (B ⧸ J)) _ _ _ _ :=
    { __ := eB.toAddEquiv
      map_smul' := by
        intro a x
        rw [Algebra.smul_def, Algebra.smul_def]
        change eB (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B) a * x) =
          algebraMap (IsLocalRing.ResidueField (A ⧸ I))
            (IsLocalRing.ResidueField (B ⧸ J)) (eA a) * eB x
        rw [map_mul]
        congr 1
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
        rfl }
  let bResid := Module.Basis.mapSemilinear eA b₀ eResid
  have hbResid (i : ι) : bResid i =
      IsLocalRing.residue (B ⧸ J) (Ideal.Quotient.mk J (v i)) := by
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
  let _ : Module.Flat (A ⧸ I) (B ⧸ J) := flat_quotient_map A B I
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (A ⧸ I)) := by
    refine ⟨n, ?_⟩
    rw [← hmaxA, ← Ideal.map_pow]
    change Ideal.map qA I = 0
    exact Ideal.map_quotient_self I
  obtain ⟨b, hb⟩ := exists_basis_of_flat_of_isNilpotent_maximalIdeal hnil
    (fun i : ι ↦ Ideal.Quotient.mk J (v i)) bTensor (by
      funext i
      exact (hbTensor i).symm)
  exact ⟨b, hb⟩

include hmax in
/-- The compatible lifted residue basis defines a map from a free module that is bijective
modulo every power of the base maximal ideal. -/
theorem exists_linearCombination_reduceModIdeal_bijective_of_flat :
    ∃ v : Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) → B,
      ∀ n : ℕ, Function.Bijective
        ((Finsupp.linearCombination A v).reduceModIdeal
          (IsLocalRing.maximalIdeal A ^ n)) := by
  obtain ⟨v, hv⟩ := exists_basis_quotient_maximalIdeal_powers_of_flat hmax
  refine ⟨v, ?_⟩
  intro n
  let ι := Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B)
  by_cases hn : n = 0
  · subst n
    let _ : Subsingleton
        ((ι →₀ A) ⧸ (IsLocalRing.maximalIdeal A ^ 0 • (⊤ : Submodule A (ι →₀ A)))) :=
      ⟨fun x y ↦ by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact (Submodule.Quotient.eq _).2 (by
          rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
          exact (show x - y ∈ (⊤ : Submodule A _) from Submodule.mem_top))⟩
    let _ : Subsingleton
        (B ⧸ (IsLocalRing.maximalIdeal A ^ 0 • ⊤ : Submodule A B)) :=
      ⟨fun x y ↦ by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact (Submodule.Quotient.eq _).2 (by
          rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
          exact (show x - y ∈ (⊤ : Submodule A _) from Submodule.mem_top))⟩
    exact Function.bijective_of_subsingleton' _
  obtain ⟨b, hb⟩ := hv n hn
  let I := IsLocalRing.maximalIdeal A ^ n
  let eDom := Finsupp.quotientSMulTopEquiv I ι
  let eCod := quotientSMulTopEquivQuotientMap (B := B) I
  let red := (Finsupp.linearCombination A v).reduceModIdeal I
  have hcomm : eCod.toLinearMap.comp red =
      b.repr.symm.toLinearMap.comp eDom.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.reduceModIdeal_apply]
    change quotientSMulTopEquivQuotientMap I
      (Submodule.Quotient.mk ((Finsupp.linearCombination A v) x)) =
      b.repr.symm (Finsupp.quotientSMulTopEquiv I ι (Submodule.Quotient.mk x))
    rw [quotientSMulTopEquivQuotientMap_mk, Finsupp.quotientSMulTopEquiv_mk]
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

include hmax in
/-- For a flat local algebra `B` over a Noetherian local ring `A` with `𝔪_A B = 𝔪_B`, the
`𝔪_A`-adic completion of `B` is flat over `A`: it is the completion of a free `A`-module
(Tags `07QM`, `06LE`).  This is the flatness-over-each-stage input of Stacks Tag `06LJ`. -/
theorem adicCompletion_flat_of_flat_of_map_maximalIdeal [IsNoetherianRing A] :
    Module.Flat A (AdicCompletion (IsLocalRing.maximalIdeal A) B) := by
  obtain ⟨v, hv⟩ := exists_linearCombination_reduceModIdeal_bijective_of_flat hmax
  let e := LinearEquiv.ofBijective _
    (AdicCompletion.map_bijective_of_reduceModIdeal (IsLocalRing.maximalIdeal A) _ hv)
  let _ := AdicCompletion.finsupp_flat_of_isNoetherian (IsLocalRing.maximalIdeal A)
    (Module.Free.ChooseBasisIndex (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
  exact Module.Flat.of_linearEquiv (e.symm.restrictScalars A)

end GeneralCompletion

section CompletionComparison

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  (I : Ideal A) (M : Type w) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- The `I ^ n`-adic submodule of a `B`-module is the restriction of its `(I B) ^ n`-adic
submodule. -/
theorem smul_top_eq_restrictScalars_map_pow_smul_top (n : ℕ) :
    (I ^ n • ⊤ : Submodule A M) =
      ((I.map (algebraMap A B)) ^ n • (⊤ : Submodule B M)).restrictScalars A := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

/-- The level-`n` comparison between the `I`-adic and the `I B`-adic quotients of a `B`-module. -/
noncomputable def quotientPowSMulTopEquivMap (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule A M)) ≃ₗ[A]
      M ⧸ ((I.map (algebraMap A B)) ^ n • (⊤ : Submodule B M)) :=
  Submodule.quotEquivOfEq _ _ (smul_top_eq_restrictScalars_map_pow_smul_top I M n) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv A _

@[simp]
theorem quotientPowSMulTopEquivMap_mk (n : ℕ) (x : M) :
    quotientPowSMulTopEquivMap (B := B) I M n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  rfl

@[simp]
theorem quotientPowSMulTopEquivMap_symm_mk (n : ℕ) (x : M) :
    (quotientPowSMulTopEquivMap (B := B) I M n).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  rfl

/-- The level comparisons commute with the transition maps. -/
theorem quotientPowSMulTopEquivMap_transitionMap {m n : ℕ} (hmn : m ≤ n)
    (z : M ⧸ (I ^ n • ⊤ : Submodule A M)) :
    AdicCompletion.transitionMap (I.map (algebraMap A B)) M hmn
        (quotientPowSMulTopEquivMap (B := B) I M n z) =
      quotientPowSMulTopEquivMap (B := B) I M m (AdicCompletion.transitionMap I M hmn z) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

/-- The inverse level comparisons commute with the transition maps. -/
theorem quotientPowSMulTopEquivMap_symm_transitionMap {m n : ℕ} (hmn : m ≤ n)
    (z : M ⧸ ((I.map (algebraMap A B)) ^ n • (⊤ : Submodule B M))) :
    AdicCompletion.transitionMap I M hmn
        ((quotientPowSMulTopEquivMap (B := B) I M n).symm z) =
      (quotientPowSMulTopEquivMap (B := B) I M m).symm
        (AdicCompletion.transitionMap (I.map (algebraMap A B)) M hmn z) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

/-- The `I`-adic completion of a `B`-module agrees, as an `A`-module, with its
`I B`-adic completion: the two inverse systems have the same terms. -/
noncomputable def adicCompletionEquivMapAlgebraMap :
    AdicCompletion I M ≃ₗ[A] AdicCompletion (I.map (algebraMap A B)) M where
  toFun x := ⟨fun n ↦ quotientPowSMulTopEquivMap (B := B) I M n (x.val n), fun hmn ↦
    (quotientPowSMulTopEquivMap_transitionMap I M hmn (x.val _)).trans
      (congrArg _ (x.property hmn))⟩
  invFun x := ⟨fun n ↦ (quotientPowSMulTopEquivMap (B := B) I M n).symm (x.val n), fun hmn ↦
    (quotientPowSMulTopEquivMap_symm_transitionMap I M hmn (x.val _)).trans
      (congrArg _ (x.property hmn))⟩
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact map_add _ (x.val n) (y.val n)
  map_smul' a x := by
    apply AdicCompletion.ext
    intro n
    exact map_smul _ a (x.val n)
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact LinearEquiv.symm_apply_apply _ (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact LinearEquiv.apply_symm_apply _ (x.val n)

end CompletionComparison

/-- For a flat local algebra `B` over a Noetherian local ring `A` with `𝔪_A B = 𝔪_B`, the
`𝔪_B`-adic completion of `B` is flat over `A`.  This is the form of Stacks Tag `06LJ`'s
"completion of a free module" step (Tags `07QM`, `06LE`) used for each stage. -/
theorem maximalAdicCompletion_flat_of_flat_of_map_maximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [Algebra A B]
    [Module.Flat A B] [IsLocalHom (algebraMap A B)]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B) :
    Module.Flat A (AdicCompletion (IsLocalRing.maximalIdeal B) B) := by
  let _ := adicCompletion_flat_of_flat_of_map_maximalIdeal hmax
  let e := adicCompletionEquivMapAlgebraMap (B := B) (IsLocalRing.maximalIdeal A) B
  rw [hmax] at e
  exact Module.Flat.of_linearEquiv e.symm

/-- Flatness over a ring can be checked on rings mapping to it: if every finite family of
scalars comes from some `T → S` over which `M` is flat, then `M` is flat over `S`.  This is the
equational-criterion form of Stacks Algebra Lemma `10.39.6` (flatness over every stage of a
filtered colimit implies flatness over the colimit). -/
theorem Module.Flat.of_forall_exists_flat_algebra
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
    (h : ∀ (l : ℕ) (c : Fin l → S), ∃ (T : Type u) (_ : CommRing T) (_ : Algebra T S)
      (_ : Module T M) (_ : IsScalarTower T S M) (_ : Module.Flat T M) (t : Fin l → T),
        ∀ i, algebraMap T S (t i) = c i) :
    Module.Flat S M := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l c x hx
  obtain ⟨T, _, _, _, _, _, t, ht⟩ := h l c
  have hxT : ∑ i, t i • x i = 0 := by
    simpa only [← algebraMap_smul S (t _) (x _), ht] using hx
  obtain ⟨k, a, y, hxy, hta⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hxT
  refine ⟨k, fun i j ↦ algebraMap T S (a i j), y, ?_, ?_⟩
  · intro i
    rw [hxy i]
    simp only [algebraMap_smul]
  · intro j
    have := congrArg (algebraMap T S) (hta j)
    simpa only [map_sum, smul_eq_mul, map_mul, ht, map_zero] using this

namespace PointedEtaleNeighborhood

section StageFlat

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- The strict local colimit is flat over every pointed étale stage, through the canonical stage
map.  As for flatness over the base (`localColimit_flat`), a relation in the colimit is realized
in a later stage, which is étale and hence flat over the earlier one. -/
theorem localColimit_flat_stage (X : PointedEtaleNeighborhood R Ω) :
    letI := (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom.toAlgebra
    Module.Flat X (LocalColimit R Ω) := by
  let : Algebra X (LocalColimit R Ω) :=
    (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom.toAlgebra
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f y hy
  classical
  obtain ⟨Y, hY⟩ := exists_stage_containing_finite_localColimit_set
    (R := R) (Ω := Ω) (Set.range y) (Set.finite_range y)
  choose yY hyY using fun i : Fin l ↦ hY (Set.mem_range_self i)
  obtain ⟨Z, ⟨g₁⟩, ⟨g₂⟩⟩ := exists_common_refinement X Y
  have h₁ (a : X) : toLocalColimitAlgHom (R := R) (Ω := Ω) Z (g₁.hom a) =
      toLocalColimitAlgHom (R := R) (Ω := Ω) X a :=
    DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) g₁) a
  have h₂ (a : Y) : toLocalColimitAlgHom (R := R) (Ω := Ω) Z (g₂.hom a) =
      toLocalColimitAlgHom (R := R) (Ω := Ω) Y a :=
    DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) g₂) a
  let z : Z := ∑ i, g₁.hom (f i) * g₂.hom (yY i)
  have hz : toLocalColimitAlgHom (R := R) (Ω := Ω) Z z = 0 := by
    have hy' : ∑ i, toLocalColimitAlgHom (R := R) (Ω := Ω) X (f i) * y i = 0 := hy
    simpa only [z, map_sum, map_mul, h₁, h₂, hyY] using hy'
  obtain ⟨W, h, hh⟩ :=
    exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero (R := R) (Ω := Ω) Z z hz
  have h₃ (a : Z) : toLocalColimitAlgHom (R := R) (Ω := Ω) W (h.hom a) =
      toLocalColimitAlgHom (R := R) (Ω := Ω) Z a :=
    DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) h) a
  let k : X ⟶ W := g₁ ≫ h
  let : Algebra X W := k.hom.toRingHom.toAlgebra
  have : IsScalarTower R X W :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (k.hom.commutes r).symm
  have : Algebra.Etale X W := Algebra.Etale.of_restrictScalars R X W
  have hrel : ∑ i, f i • h.hom (g₂.hom (yY i)) = 0 := by
    have hh' := hh
    simp only [z, map_sum, map_mul] at hh'
    exact hh'
  obtain ⟨m, a, w, hxy, hfa⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨m, a, fun j ↦ toLocalColimitAlgHom (R := R) (Ω := Ω) W (w j), ?_, hfa⟩
  intro i
  calc
    y i = toLocalColimitAlgHom (R := R) (Ω := Ω) Y (yY i) := (hyY i).symm
    _ = toLocalColimitAlgHom (R := R) (Ω := Ω) W (h.hom (g₂.hom (yY i))) := by
      rw [h₃, h₂]
    _ = toLocalColimitAlgHom (R := R) (Ω := Ω) W (∑ j, a i j • w j) :=
      congrArg _ (hxy i)
    _ = ∑ j, a i j • toLocalColimitAlgHom (R := R) (Ω := Ω) W (w j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      change toLocalColimitAlgHom (R := R) (Ω := Ω) W (h.hom (g₁.hom (a i j))) = _
      rw [h₃, h₁]
      rfl

end StageFlat

section StageLocal

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

/-- The prime of a pointed étale stage at its geometric point. -/
noncomputable abbrev stagePrime (X : PointedEtaleNeighborhood R Ω) : Ideal X :=
  RingHom.ker X.point.toRingHom

instance stagePrime_isPrime (X : PointedEtaleNeighborhood R Ω) : (stagePrime X).IsPrime :=
  RingHom.ker_isPrime _

/-- The local ring of a pointed étale stage at its geometric point. -/
noncomputable abbrev StageLocal (X : PointedEtaleNeighborhood R Ω) : Type u :=
  Localization.AtPrime (stagePrime X)

/-- Stage elements that do not vanish at the point become units in the strict local colimit. -/
theorem isUnit_toLocalColimitAlgHom_of_point_ne_zero
    (X : PointedEtaleNeighborhood R Ω) (x : X) (hx : X.point x ≠ 0) :
    IsUnit (toLocalColimitAlgHom (R := R) (Ω := Ω) X x) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro h0
  apply hx
  rw [← residueFieldAlgEquiv_residue_toLocalColimitAlgHom (R := R) (Ω := Ω) X x, h0, map_zero]

/-- Stage elements that vanish at the point land in the maximal ideal of the colimit. -/
theorem toLocalColimitAlgHom_mem_maximalIdeal_of_point_eq_zero
    (X : PointedEtaleNeighborhood R Ω) (x : X) (hx : X.point x = 0) :
    toLocalColimitAlgHom (R := R) (Ω := Ω) X x ∈
      IsLocalRing.maximalIdeal (LocalColimit R Ω) := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  apply (residueFieldAlgEquiv (R := R) (Ω := Ω)).injective
  rw [residueFieldAlgEquiv_residue_toLocalColimitAlgHom (R := R) (Ω := Ω) X x, hx, map_zero]

/-- The canonical map from the local ring of a stage to the strict local colimit. -/
noncomputable def stageLocalToLocalColimit (X : PointedEtaleNeighborhood R Ω) :
    StageLocal X →+* LocalColimit R Ω :=
  IsLocalization.lift (M := (stagePrime X).primeCompl)
    (g := (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom)
    (fun s ↦ isUnit_toLocalColimitAlgHom_of_point_ne_zero X s s.2)

theorem stageLocalToLocalColimit_algebraMap (X : PointedEtaleNeighborhood R Ω) (x : X) :
    stageLocalToLocalColimit X (algebraMap X (StageLocal X) x) =
      toLocalColimitAlgHom (R := R) (Ω := Ω) X x :=
  IsLocalization.lift_eq _ x

/-- The maximal ideal of a stage local ring extends to the maximal ideal of the strict local
colimit. -/
theorem map_maximalIdeal_stageLocal (X : PointedEtaleNeighborhood R Ω) :
    (IsLocalRing.maximalIdeal (StageLocal X)).map (stageLocalToLocalColimit X) =
      IsLocalRing.maximalIdeal (LocalColimit R Ω) := by
  have hcomp : (stageLocalToLocalColimit X).comp (algebraMap X (StageLocal X)) =
      (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom :=
    RingHom.ext fun x ↦ stageLocalToLocalColimit_algebraMap X x
  have hL : (IsLocalRing.maximalIdeal (StageLocal X)).map (stageLocalToLocalColimit X) =
      (stagePrime X).map (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp]
  rw [hL]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact toLocalColimitAlgHom_mem_maximalIdeal_of_point_eq_zero X x hx
  · rw [← map_maximalIdeal_localColimit (R := R) (Ω := Ω)]
    have hR : (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom.comp (algebraMap R X) =
        algebraMap R (LocalColimit R Ω) :=
      RingHom.ext fun r ↦ (toLocalColimitAlgHom (R := R) (Ω := Ω) X).commutes r
    rw [← hR, ← Ideal.map_map]
    apply Ideal.map_mono
    rw [Ideal.map_le_iff_le_comap]
    rw [← point_ker_under (R := R) (Ω := Ω) X]

/-- The maximal-adic completion of the strict local colimit is flat over the local ring of every
pointed étale stage.  This is the "flat over each `R_i`" step of Stacks Tag `06LJ`. -/
theorem localColimit_completion_flat_stageLocal [IsNoetherianRing R]
    (X : PointedEtaleNeighborhood R Ω) :
    letI := (stageLocalToLocalColimit X).toAlgebra
    Module.Flat (StageLocal X)
      (AdicCompletion (IsLocalRing.maximalIdeal (LocalColimit R Ω)) (LocalColimit R Ω)) := by
  let algL : Algebra (StageLocal X) (LocalColimit R Ω) := (stageLocalToLocalColimit X).toAlgebra
  let algX : Algebra X (LocalColimit R Ω) :=
    (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom.toAlgebra
  have : IsScalarTower X (StageLocal X) (LocalColimit R Ω) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (stageLocalToLocalColimit_algebraMap X x).symm
  have : Module.Flat X (LocalColimit R Ω) := localColimit_flat_stage X
  have : IsLocalizedModule (stagePrime X).primeCompl
      (LinearMap.id : LocalColimit R Ω →ₗ[X] LocalColimit R Ω) :=
    isLocalizedModule_id _ _ (StageLocal X)
  have : Module.Flat (StageLocal X) (LocalColimit R Ω) :=
    Module.Flat.of_isLocalizedModule (R := X) (StageLocal X) (stagePrime X).primeCompl
      LinearMap.id
  have hmax := map_maximalIdeal_stageLocal X
  have : IsLocalHom (algebraMap (StageLocal X) (LocalColimit R Ω)) :=
    ((IsLocalRing.local_hom_TFAE _).out 3 1).mp hmax.le
  exact maximalAdicCompletion_flat_of_flat_of_map_maximalIdeal hmax

end StageLocal

section Main

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field Ω]
  [Algebra R Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

/-- **Stacks Tag `06LJ` (c), strict case.**  For a Noetherian local ring `R`, the strict
henselization `Rˢʰ` is flat into its maximal-adic completion.

Route: the completion is flat over the local ring of every pointed étale stage (it is the
completion of a free module over that stage, Tags `07QM`, `06LE`), and flatness over all stages
gives flatness over the filtered colimit (Algebra Lemma `10.39.6`, via the equational criterion).
Divergence from Stacks: the stages are not identified with strict henselizations of themselves;
the free-completion argument is applied directly to the flat local map from each stage. -/
@[stacks 06LJ "part (c), strict case, for the pcf colimit model `LocalColimit R Ω` of `R^sh`, \
  Ω any field over κ(𝔪): it is flat into its completion"]
theorem localColimit_completion_flat :
    Module.Flat (LocalColimit R Ω)
      (AdicCompletion (IsLocalRing.maximalIdeal (LocalColimit R Ω)) (LocalColimit R Ω)) := by
  apply Module.Flat.of_forall_exists_flat_algebra
  intro l c
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set
    (R := R) (Ω := Ω) (Set.range c) (Set.finite_range c)
  choose x hx using fun i : Fin l ↦ hX (Set.mem_range_self i)
  let := (stageLocalToLocalColimit X).toAlgebra
  exact ⟨StageLocal X, inferInstance, inferInstance, inferInstance, inferInstance,
    localColimit_completion_flat_stageLocal X,
    fun i ↦ algebraMap X (StageLocal X) (x i),
    fun i ↦ (stageLocalToLocalColimit_algebraMap X (x i)).trans (hx i)⟩

/-- **Stacks Tag `06LJ`, `R ⇒ Rˢʰ`.**  The strict henselization of a Noetherian local ring is
Noetherian.  This discharges `hflat` in `localColimit_isNoetherianRing_of_completion`.

Proof as in Stacks: flatness of the completion (part (c), `localColimit_completion_flat`),
Noetherianity of the completion from the finitely generated maximal ideal `𝔪 Rˢʰ` (Tags `032B`,
`05GH`), and descent of Noetherianity along the faithfully flat completion (Algebra,
Lemma 10.164.1). -/
@[stacks 06LJ "the implication (1) ⇒ (3), for the pcf colimit model `LocalColimit R Ω` of \
  `R^sh`, Ω any field over κ(𝔪): `R` Noetherian implies it is Noetherian"]
instance localColimit_isNoetherianRing : IsNoetherianRing (LocalColimit R Ω) :=
  localColimit_isNoetherianRing_of_completion localColimit_completion_flat

/-- The strict henselization of a Noetherian local ring has the same Krull dimension as the
base (unconditional form of `ringKrullDim_localColimit`). -/
theorem ringKrullDim_localColimit_eq :
    ringKrullDim R = ringKrullDim (LocalColimit R Ω) :=
  ringKrullDim_localColimit (R := R) (Ω := Ω)

/-- The completion of the strict henselization of a Noetherian local ring is Noetherian
(Stacks Tag `06LJ` part (a), strict case).  Here it is read off from Noetherianity of `Rˢʰ`;
Stacks' argument for (a) (the maximal ideal `𝔪 Rˢʰ` is finitely generated, Algebra 10.160.3) is
the one used inside `localColimit_isNoetherianRing_of_completion`. -/
@[stacks 06LJ "part (a), strict case, for the pcf colimit model `LocalColimit R Ω` of `R^sh`, \
  Ω any field over κ(𝔪): its completion is Noetherian"]
theorem localColimit_completion_isNoetherianRing :
    IsNoetherianRing
      (AdicCompletion (IsLocalRing.maximalIdeal (LocalColimit R Ω)) (LocalColimit R Ω)) :=
  AdicCompletion.isNoetherianRing_of_maximalIdeal_fg
    (IsLocalRing.maximalIdeal (LocalColimit R Ω)).fg_of_isNoetherianRing

end Main

/-- **Regularity ascends to the strict henselization** (the `R ⇒ Rˢʰ` direction of Stacks Tag
`06LN`), now unconditional. -/
theorem localColimit_isRegularLocalRing
    {R Ω : Type u} [CommRing R] [IsRegularLocalRing R] [Field Ω]
    [Algebra R Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
    [IsSepClosure (IsLocalRing.ResidueField R) Ω] :
    IsRegularLocalRing (LocalColimit R Ω) :=
  localColimit_isRegularLocalRing_of_isNoetherianRing

end PointedEtaleNeighborhood

#print axioms quotientSMulTopEquivQuotientMap
#print axioms quotientSMulTopEquivQuotientMap_mk
#print axioms exists_basis_quotient_maximalIdeal_powers_of_flat
#print axioms exists_linearCombination_reduceModIdeal_bijective_of_flat
#print axioms adicCompletion_flat_of_flat_of_map_maximalIdeal
#print axioms smul_top_eq_restrictScalars_map_pow_smul_top
#print axioms quotientPowSMulTopEquivMap
#print axioms quotientPowSMulTopEquivMap_mk
#print axioms quotientPowSMulTopEquivMap_symm_mk
#print axioms quotientPowSMulTopEquivMap_transitionMap
#print axioms quotientPowSMulTopEquivMap_symm_transitionMap
#print axioms adicCompletionEquivMapAlgebraMap
#print axioms maximalAdicCompletion_flat_of_flat_of_map_maximalIdeal
#print axioms Module.Flat.of_forall_exists_flat_algebra
#print axioms PointedEtaleNeighborhood.localColimit_flat_stage
#print axioms PointedEtaleNeighborhood.stagePrime
#print axioms PointedEtaleNeighborhood.stagePrime_isPrime
#print axioms PointedEtaleNeighborhood.StageLocal
#print axioms PointedEtaleNeighborhood.isUnit_toLocalColimitAlgHom_of_point_ne_zero
#print axioms PointedEtaleNeighborhood.toLocalColimitAlgHom_mem_maximalIdeal_of_point_eq_zero
#print axioms PointedEtaleNeighborhood.stageLocalToLocalColimit
#print axioms PointedEtaleNeighborhood.stageLocalToLocalColimit_algebraMap
#print axioms PointedEtaleNeighborhood.map_maximalIdeal_stageLocal
#print axioms PointedEtaleNeighborhood.localColimit_completion_flat_stageLocal
#print axioms PointedEtaleNeighborhood.localColimit_completion_flat
#print axioms PointedEtaleNeighborhood.localColimit_isNoetherianRing
#print axioms PointedEtaleNeighborhood.ringKrullDim_localColimit_eq
#print axioms PointedEtaleNeighborhood.localColimit_completion_isNoetherianRing
#print axioms PointedEtaleNeighborhood.localColimit_isRegularLocalRing

end Pcf.Stacks
