/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
-- Vendored into pcf from mathlib4 PR #29802 (author Nailin Guan, GitHub `Thmoas-Guan`),
-- head commit 8183b4ca0327e9a3f9c994493a49c8c5eb5ef0fc,
-- file `Mathlib/RingTheory/Depth/Basic.lean` (only the lines the PR adds).
-- All declarations are placed in the namespace `Pcf.Vendor` so that nothing clashes with
-- Mathlib when the PR lands upstream. Adaptations to the pcf Mathlib pin are marked `pcf:`.
module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.Tactic.ENatToNat

/-!
# Depth: quotients by regular elements and sequences

The lemmas appended to `Mathlib/RingTheory/Depth/Basic.lean` by mathlib4 PR #29802, split off into
their own file because the pin already contains the rest of that file.

* `IsLocalRing.depth_quotSMulTop_succ_eq_depth` : For `R` local, a `R`-module `M` and a
  `M`-regular element `x` in `maximalIdeal R`,
  `IsLocalRing.depth (QuotSMulTop x M) + 1 = IsLocalRing.depth M`

* `IsLocalRing.depth_quotient_isRegular_add_length_eq_depth` : For `R` local, a `R`-module
  `M` and a `M`-regular sequence `rs` in `maximalIdeal R`,
  `depth N (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M)) + rs.length = depth N M`
-/

@[expose] public section

namespace Pcf.Vendor

open IsLocalRing LinearMap Module

universe v u

open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular

variable {R : Type u} [CommRing R] [Small.{v} R]

section depth

lemma ModuleCat.depth_quotSMulTop_succ_eq_depth (N M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ Module.annihilator R N) :
    N.depth ↧(QuotSMulTop x M) + 1 = N.depth M := by
  simp only [ModuleCat.depth, add_comm]
  have iff (i : ℕ) : Subsingleton (Ext N ↧(QuotSMulTop x M) i) ↔
    (Subsingleton (Ext N M i) ∧ Subsingleton (Ext N M (i + 1))) := by
    refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h1, h3⟩ ↦ ?_⟩
    · exact @Function.Injective.subsingleton _ _ _ ((AddCommGrpCat.mono_iff_injective _).mp <|
        (Ext.covariant_sequence_exact₂' N reg.smulShortComplex_shortExact i).mono_g
        (Ext.postcomp_smul_id_eq_zero_of_mem_annihilator mem i)) h
    · exact @Function.Surjective.subsingleton _ _ _ h ((AddCommGrpCat.epi_iff_surjective _).mp <|
        (Ext.covariant_sequence_exact₁' N reg.smulShortComplex_shortExact i (i + 1) rfl).epi_f
        (Ext.postcomp_smul_id_eq_zero_of_mem_annihilator mem (i + 1)))
    · exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' N reg.smulShortComplex_shortExact i (i + 1) rfl)
        ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr h1).eq_zero_of_src _)
        ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr h3).eq_zero_of_tgt _)
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    match i with
    | 0 =>
      rw [Ext.addEquiv₀.subsingleton_congr, ModuleCat.homAddEquiv.subsingleton_congr]
      exact linearMap_subsingleton_of_mem_annihilator reg mem
    | i + 1 =>
      have : i < n := by simpa [add_comm 1 n] using hi
      exact ((iff i).mp (hn i this)).2
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        enat_to_nat
        omega
      rw [add_comm, ← this]
      apply add_le_add_left
      apply le_sSup
      intro i hi
      have lt2 : i + 1 < n := by
        enat_to_nat
        omega
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

lemma Ideal.depth_quotSMulTop_succ_eq_depth (I : Ideal R) (M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ I) :
    I.depth ↧(QuotSMulTop x M) + 1 = I.depth M := by
  apply ModuleCat.depth_quotSMulTop_succ_eq_depth _ M x reg
  simpa [LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ I)), Ideal.annihilator_quotient]

lemma IsLocalRing.depth_quotSMulTop_succ_eq_depth [IsLocalRing R] (M : ModuleCat.{v} R)
    (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = IsLocalRing.depth M :=
  Ideal.depth_quotSMulTop_succ_eq_depth (maximalIdeal R) M x reg mem -- pcf: no dot notation

lemma ModuleCat.depth_quotient_isRegular_add_length_eq_depth (N M : ModuleCat.{v} R)
    (rs : List R) (reg : IsWeaklyRegular M rs) (h : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    N.depth ↧(M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M)) + rs.length =
    N.depth M := by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero =>
    rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using depth_eq_of_iso_right N (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  | succ n hn =>
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [depth_eq_of_iso_right N
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso,
        ← depth_quotSMulTop_succ_eq_depth N M x this (h x List.mem_cons_self),
        ← hn ↧(QuotSMulTop x M) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
        (fun r hr ↦ h r (List.mem_cons_of_mem x hr)) len, add_assoc]

lemma Ideal.depth_quotient_isRegular_add_length_eq_ideal_depth (I : Ideal R)
    (M : ModuleCat.{v} R) (rs : List R) (reg : IsWeaklyRegular M rs) (h : ∀ r ∈ rs, r ∈ I) :
    I.depth ↧(M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M)) + rs.length =
    I.depth M := by
  apply ModuleCat.depth_quotient_isRegular_add_length_eq_depth _ M rs reg -- pcf: qualified
  simpa [(Shrink.linearEquiv R (R ⧸ I)).annihilator_eq , Ideal.annihilator_quotient] using h

lemma IsLocalRing.depth_quotient_isRegular_add_length_eq_depth [IsLocalRing R]
    (M : ModuleCat.{v} R) (rs : List R) (reg : IsRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    IsLocalRing.depth M := by
  apply Ideal.depth_quotient_isRegular_add_length_eq_ideal_depth _ M rs reg.1
  intro r hr
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  by_contra isu
  absurd reg.2
  simp [eq_top_of_isUnit_mem (ofList rs) (Ideal.subset_span hr) isu]

section ring

private instance (R : Type*) [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
    IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma IsLocalRing.depth_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] (e : R ≃+* R') :
    IsLocalRing.depth (ModuleCat.of R R) = IsLocalRing.depth (ModuleCat.of R' R') := by
  simp only [IsLocalRing.depth_eq_sSup_length_isRegular] -- pcf: qualified
  congr!
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · use rs.map e.toRingHom, (e.toSemilinearEquiv.isRegular_congr' rs).mp reg
    simpa [len]
  · use rs.map e.symm.toRingHom, (e.toSemilinearEquiv.symm.isRegular_congr' rs).mp reg
    simpa [len]

lemma IsLocalRing.depth_eq_of_algebraMap_surjective [IsLocalRing R] [IsNoetherianRing R]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra R S] [Small.{v} S] [IsNoetherianRing S]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module S M]
    [IsScalarTower R S M] [Nontrivial M] (surj : Function.Surjective (algebraMap R S)) :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S M) := by
  have : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  have loc_hom : IsLocalHom (algebraMap R S) := surj.isLocalHom _
  simp only [IsLocalRing.depth_eq_sSup_length_isRegular] -- pcf: qualified
  congr!
  rename_i n
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · have mem' : ∀ r ∈ rs.map (algebraMap R S), r ∈ maximalIdeal S := by
      intro r hr
      simp only [List.mem_map] at hr
      rcases hr with ⟨r', hr', eq⟩
      simpa [← eq] using mem r' hr'
    have reg' : IsRegular M (rs.map (algebraMap R S)) := by
      refine ⟨(isWeaklyRegular_map_algebraMap_iff S M rs).mpr reg.1, ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs.map (algebraMap R S), reg', mem'
    simpa
  · rcases List.map_surjective_iff.mpr surj rs with ⟨rs', hrs'⟩
    have mem' : ∀ r ∈ rs', r ∈ maximalIdeal R := by
      intro r hr
      have : algebraMap R S r ∈ maximalIdeal S := by
        apply mem
        simpa only [← hrs'] using List.mem_map_of_mem hr
      simpa using this
    have reg' : IsRegular M rs' := by
      refine ⟨(isWeaklyRegular_map_algebraMap_iff S M rs').mp (by simpa [hrs'] using reg.1), ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs', reg', mem'
    simpa [← hrs'] using len

omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_isSMulRegular_succ_eq_depth [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
      have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ x • (⊤ : Ideal R)) (R ⧸ x • (⊤ : Ideal R))) + 1 =
    IsLocalRing.depth (ModuleCat.of R R) := by
  have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
    Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
  have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  rw [← IsLocalRing.depth_quotSMulTop_succ_eq_depth (ModuleCat.of R R) x reg mem, eq_comm]
  congr 1
  apply depth_eq_of_algebraMap_surjective _
  simpa only [Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective

omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_span_isSMulRegular_succ_eq_depth [IsLocalRing R]
    [IsNoetherianRing R] (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      have : Nontrivial (R ⧸ Ideal.span {x}) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) + 1 =
    IsLocalRing.depth (ModuleCat.of R R) := by
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    have : Nontrivial (R ⧸ Ideal.span {x}) :=
      Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
      Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have := Submodule.ideal_span_singleton_smul x (⊤ :Ideal R)
  simp only [smul_eq_mul, mul_top] at this
  rw [IsLocalRing.depth_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R this).toRingEquiv,
    IsLocalRing.depth_quotient_isSMulRegular_succ_eq_depth x reg mem]

omit [Small.{v, u} R] in
lemma IsLocalRing.ring_depth_quotient_isRegular_add_length_eq_depth [IsLocalRing R]
    [IsNoetherianRing R] (rs : List R) (reg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ Ideal.ofList rs) :=
      have : Nontrivial (R ⧸ Ideal.ofList rs) := Submodule.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top IsPrime.ne_top' (span_le.mpr mem))
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList rs)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ Ideal.ofList rs)
      (R ⧸ Ideal.ofList rs)) + rs.length =
    IsLocalRing.depth (ModuleCat.of R R) := by
  generalize len : rs.length = n
  induction n generalizing R rs
  · let e : R ⧸ ofList rs ≃+* R :=
      (RingEquiv.ofBijective _ ((Ideal.Quotient.mk_bijective_iff_eq_bot (Ideal.ofList rs)).mpr
        (by simp [List.length_eq_zero_iff.mp len]))).symm
    have : IsLocalRing (R ⧸ ofList rs) := RingEquiv.isLocalRing e.symm
    simpa using IsLocalRing.depth_eq_of_ringEquiv e
  · rename_i n hn _ _ _
    match rs with
    | [] => simp at len
    | x :: rs' =>
      have : IsLocalRing (R ⧸ Ideal.ofList (x :: rs')) :=
        have : Nontrivial (R ⧸ Ideal.ofList (x :: rs')) := Submodule.Quotient.nontrivial_iff.mpr
          (ne_top_of_le_ne_top IsPrime.ne_top' (span_le.mpr mem))
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [isWeaklyRegular_cons_iff] at reg
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc,
        ← depth_quotient_isSMulRegular_succ_eq_depth x reg.1 mem.1]
      have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul] using mem.1)
      have loc_hom : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
        IsLocalRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have mem' : ∀ r ∈ List.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))) rs',
        r ∈ maximalIdeal (R ⧸ x • (⊤ : Ideal R)) := by
        intro r hr
        rcases List.mem_map.mp hr with ⟨r', hr', eq⟩
        simpa [← eq] using mem.2 r' hr'
      rw [← hn (rs'.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))))
        ((isWeaklyRegular_map_algebraMap_iff (R ⧸ x • (⊤ : Ideal R)) _ rs').mpr reg.2) mem'
          ((rs'.length_map _).trans len)]
      congr 2
      let e : R ⧸ ofList (x :: rs') ≃+* ((R ⧸ x • (⊤ : Ideal R)) ⧸
        ofList (rs'.map (Ideal.Quotient.mk (x • (⊤ : Ideal R))))) := by
        rw [Ideal.ofList_cons, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top,
          ← map_ofList]
        exact (DoubleQuot.quotQuotEquivQuotSup _ _).symm
      have := e.isLocalRing
      exact IsLocalRing.depth_eq_of_ringEquiv e

end ring

end depth

end Pcf.Vendor
