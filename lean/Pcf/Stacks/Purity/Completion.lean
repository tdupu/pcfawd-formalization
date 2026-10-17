/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Pcf.Stacks.Abhyankar.StrictHenselizationRegularity

/-!
# Completion facts for the complete-case hypersurface lifting route

This file collects the completion inputs of the proof of Stacks Tag `0BMA` (purity for regular
local rings) via complete regular local rings.

## Completeness

* `Pcf.Stacks.IsAdicComplete.of_le` (Stacks `090T`): if `I ⊆ J`, `I` is finitely generated and
  `M` is `J`-adically complete, then `M` is `I`-adically complete.
* `Pcf.Stacks.isAdicComplete_of_finite`: a finite module over a Noetherian ring that is
  `I`-adically complete is `I`-adically complete (the identity `M^∧ = M ⊗_R R^∧` of Stacks
  `00MA (3)`).
* `Pcf.Stacks.isAdicComplete_map_of_finite`: the same for the extended ideal on a module over a
  finite algebra; in particular `Pcf.Stacks.isAdicComplete_quotient` and
  `Pcf.Stacks.isAdicComplete_maximalIdeal_quotient` (`A ⧸ J` is complete).
* `Pcf.Stacks.isAdicComplete_span_singleton_of_finite` and
  `Pcf.Stacks.isAdicComplete_map_span_singleton_of_finite`: over a complete Noetherian local
  ring, a finite module (or finite algebra) is `(f)`-adically complete for every `f ∈ m`.

## The completion of a regular local ring

For a Noetherian local ring `A` with completion `Â = AdicCompletion (maximalIdeal A) A`:

* `Â` is Noetherian (instance, from pcf's Stacks `05GH`/`032B` route) and local, complete for
  its maximal ideal, and `m_A Â = m_Â` (Mathlib);
* `A → Â` is faithfully flat (Stacks `00MC`);
* `dim Â = dim A` (Stacks `07NV`);
* if `A` is regular, so is `Â` (Stacks `07NY`, forward direction; instance).
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Pcf.Stacks

section Tag090T

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- An element of `span s • P` (with `s` a finite set of ring elements) is a finite sum
`∑ a ∈ s, a • z a` with all `z a ∈ P`. -/
theorem exists_sum_smul_of_mem_span_smul (s : Finset R) (P : Submodule R M) {x : M}
    (hx : x ∈ Ideal.span (s : Set R) • P) :
    ∃ z : R → M, (∀ a ∈ s, z a ∈ P) ∧ x = ∑ a ∈ s, a • z a := by
  classical
  induction hx using Submodule.smul_induction_on' with
  | smul r hr p hp =>
    obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.mp hr
    refine ⟨fun a ↦ c a • p, fun a _ ↦ P.smul_mem _ hp, ?_⟩
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [smul_eq_mul, mul_comm, mul_smul]
  | add x _ y _ hx hy =>
    obtain ⟨zx, hzx, rfl⟩ := hx
    obtain ⟨zy, hzy, rfl⟩ := hy
    refine ⟨zx + zy, fun a ha ↦ P.add_mem (hzx a ha) (hzy a ha), ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Pi.add_apply, smul_add]

/-- The closedness step in the proof of Stacks `090T`.  Let `M` be `J`-adically complete and
`K` finitely generated.  If `y 0 = 0`, the increments `y (m + 1) - y m` lie in `K • P m` with
`P m ⊆ J ^ m M`, and `y` converges `J`-adically to `L`, then `L ∈ K M`. -/
theorem mem_smul_top_of_sub_mem_smul_of_smodEq
    {J K : Ideal R} [IsAdicComplete J M] (hK : K.FG)
    (P : ℕ → Submodule R M) (hP : ∀ m, P m ≤ J ^ m • (⊤ : Submodule R M))
    (y : ℕ → M) (hy0 : y 0 = 0) (hy : ∀ m, y (m + 1) - y m ∈ K • P m)
    (L : M) (hL : ∀ m, y m ≡ L [SMOD (J ^ m • ⊤ : Submodule R M)]) :
    L ∈ K • (⊤ : Submodule R M) := by
  classical
  obtain ⟨s, rfl⟩ := hK
  choose z hzP hz using fun m ↦ exists_sum_smul_of_mem_span_smul s (P m) (hy m)
  -- partial sums of the coefficient sequences
  let Z : R → ℕ → M := fun a N ↦ ∑ m ∈ Finset.range N, z m a
  have hZ : ∀ a ∈ s, ∃ w : M, ∀ N, Z a N ≡ w [SMOD (J ^ N • ⊤ : Submodule R M)] := by
    intro a ha
    refine IsPrecomplete.prec inferInstance fun {m n} hmn ↦ ?_
    rw [SModEq.sub_mem]
    have hsub : Z a m - Z a n = -∑ k ∈ Finset.Ico m n, z k a := by
      simp only [Z, Finset.sum_Ico_eq_sub _ hmn, neg_sub]
    rw [hsub]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk ↦ ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1)
      (hP k (hzP k a ha))
  choose! w hw using hZ
  have hyZ : ∀ N, y N = ∑ a ∈ s, a • Z a N := by
    intro N
    induction N with
    | zero => simp [hy0, Z]
    | succ N ih =>
      have h := hz N
      rw [sub_eq_iff_eq_add] at h
      rw [h, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      simp only [Z, Finset.sum_range_succ, smul_add]
      abel
  have hLw : L = ∑ a ∈ s, a • w a := by
    rw [IsHausdorff.eq_iff_smodEq (I := J)]
    intro N
    refine (hL N).symm.trans ?_
    rw [hyZ N, SModEq.sub_mem, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun a ha ↦ ?_
    rw [← smul_sub]
    exact Submodule.smul_mem _ _ ((SModEq.sub_mem).mp (hw a ha N))
  rw [hLw]
  exact Submodule.sum_mem _ fun a ha ↦
    Submodule.smul_mem_smul (Ideal.subset_span ha) Submodule.mem_top

/-- Stacks Tag `090T`: if `I ⊆ J`, `I` is finitely generated and `M` is `J`-adically complete,
then `M` is `I`-adically complete.

Proof route: Stacks reduces to principal `I` via Tag `090S`; here the closedness of `I ^ n M`
is proved directly for all finitely generated `I` by expanding the increments of a Cauchy
sequence along finitely many generators of `I ^ n`. -/
@[stacks 090T]
theorem IsAdicComplete.of_le {I J : Ideal R} (hIJ : I ≤ J) (hI : I.FG)
    [IsAdicComplete J M] : IsAdicComplete I M where
  haus' x hx := IsHausdorff.haus (I := J) inferInstance x fun n ↦
    (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n))
  prec' f hf := by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := J) inferInstance fun {m n} hmn ↦
      (hf hmn).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ m))
    refine ⟨L, fun n ↦ ?_⟩
    have hmem : L - f n ∈ I ^ n • (⊤ : Submodule R M) := by
      refine mem_smul_top_of_sub_mem_smul_of_smodEq (J := J) (hI.pow (n := n))
        (fun m ↦ I ^ m • (⊤ : Submodule R M))
        (fun m ↦ Submodule.smul_mono_left (Ideal.pow_right_mono hIJ m))
        (fun m ↦ f (n + m) - f n) (by simp) (fun m ↦ ?_) (L - f n) (fun m ↦ ?_)
      · have h := (SModEq.sub_mem).mp (hf (Nat.le_succ (n + m)))
        rw [← Submodule.mul_smul, ← pow_add]
        have : f (n + (m + 1)) - f n - (f (n + m) - f n) = -(f (n + m) - f (n + m).succ) := by
          rw [← add_assoc]; abel
        rw [this]
        exact Submodule.neg_mem _ h
      · rw [SModEq.sub_mem, sub_sub_sub_cancel_right]
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left m n))
          ((SModEq.sub_mem).mp (hL (n + m)))
    rw [SModEq.sub_mem, ← neg_sub]
    exact Submodule.neg_mem _ hmem

end Tag090T

section FiniteModules

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A finite module over an `I`-adically complete Noetherian ring is `I`-adically complete.
This is the identity `M^∧ = M ⊗_R R^∧` of Stacks Tag `00MA (3)` combined with `R = R^∧`. -/
theorem isAdicComplete_of_finite [IsNoetherianRing R] [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  let eR : R ≃ₗ[R] AdicCompletion I R :=
    LinearEquiv.ofBijective (AdicCompletion.of I R)
      (AdicCompletion.of_bijective_iff.mpr inferInstance)
  let e : M ≃ₗ[R] AdicCompletion I M :=
    (TensorProduct.lid R M).symm ≪≫ₗ LinearEquiv.rTensor M eR ≪≫ₗ
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have he : ∀ x, e x = AdicCompletion.of I M x := by
    intro x
    have h1 : AdicCompletion.of I R 1 = 1 := map_one (algebraMap R (AdicCompletion I R))
    simp [e, eR, h1]
  refine AdicCompletion.of_bijective_iff.mp ?_
  have : ⇑(AdicCompletion.of I M) = ⇑e := funext fun x ↦ (he x).symm
  rw [this]
  exact e.bijective

/-- A module over a finite `R`-algebra `S` which is finite over the `I`-adically complete
Noetherian ring `R` is complete for the extended ideal `I S`. -/
theorem isAdicComplete_map_of_finite [IsNoetherianRing R] [IsAdicComplete I R]
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R M] :
    IsAdicComplete (I.map (algebraMap R S)) M := by
  have h := isAdicComplete_of_finite I M
  exact
    { toIsHausdorff := IsHausdorff.map_algebraMap_iff.mpr h.toIsHausdorff
      toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.mpr h.toIsPrecomplete }

/-- A finite algebra over an `I`-adically complete Noetherian ring is complete for the extended
ideal. -/
theorem isAdicComplete_map_self_of_finite [IsNoetherianRing R] [IsAdicComplete I R]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S :=
  isAdicComplete_map_of_finite I S S

/-- A quotient of an `I`-adically complete Noetherian ring is complete for the image of `I`. -/
theorem isAdicComplete_quotient [IsNoetherianRing R] [IsAdicComplete I R] (J : Ideal R) :
    IsAdicComplete (I.map (Ideal.Quotient.mk J)) (R ⧸ J) := by
  have h := isAdicComplete_map_self_of_finite I (R ⧸ J)
  rwa [Ideal.Quotient.algebraMap_eq] at h

/-- The quotient of a complete Noetherian local ring by a proper ideal is complete for its
maximal ideal. -/
theorem isAdicComplete_maximalIdeal_quotient [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    IsAdicComplete (maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
  exact isAdicComplete_quotient (maximalIdeal R) J

/-- Over a complete Noetherian local ring, a finite module is `(f)`-adically complete for every
`f` in the maximal ideal (Stacks Tag `090T` together with `isAdicComplete_of_finite`). -/
theorem isAdicComplete_span_singleton_of_finite [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] {f : R} (hf : f ∈ maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete (Ideal.span {f}) M := by
  have := isAdicComplete_of_finite (maximalIdeal R) M
  exact IsAdicComplete.of_le ((Ideal.span_singleton_le_iff_mem _).mpr hf)
    (Submodule.fg_span_singleton f)

/-- Over a complete Noetherian local ring `R`, an `S`-module that is finite over `R` (for
instance a finite `R`-algebra `S` itself) is complete for `f S`, for every `f ∈ m_R`. -/
theorem isAdicComplete_map_span_singleton_of_finite [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] {f : R} (hf : f ∈ maximalIdeal R)
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R M] :
    IsAdicComplete ((Ideal.span {f}).map (algebraMap R S)) M := by
  have h := isAdicComplete_span_singleton_of_finite hf M
  exact
    { toIsHausdorff := IsHausdorff.map_algebraMap_iff.mpr h.toIsHausdorff
      toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.mpr h.toIsPrecomplete }

end FiniteModules

section RegularCompletion

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The maximal-adic completion of a Noetherian local ring is Noetherian (Stacks Tag `0316`,
local case; proved in pcf through Tags `05GH` and `032B`). -/
@[stacks 0316 "maximal-ideal completion of a local ring"]
instance isNoetherianRing_adicCompletion :
    IsNoetherianRing (AdicCompletion (maximalIdeal A) A) :=
  AdicCompletion.isNoetherianRing_of_maximalIdeal_fg (maximalIdeal A).fg_of_isNoetherianRing

/-- The maximal ideal of the completion is the extension of the maximal ideal. -/
theorem map_maximalIdeal_adicCompletion :
    (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      maximalIdeal (AdicCompletion (maximalIdeal A) A) :=
  (AdicCompletion.maximalIdeal_eq_map (R := A)).symm

/-- Stacks Tag `00MC`, local case: the completion of a Noetherian local ring is faithfully flat
over it. -/
@[stacks 00MC "Noetherian local ring, maximal-ideal completion"]
theorem faithfullyFlat_adicCompletion :
    Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Stacks Tag `07NV`: a Noetherian local ring and its completion have the same dimension.

Proof route: Stacks compares Hilbert polynomials; here we use flatness (going down) and the
equality `m_A Â = m_Â`, so that the closed fibre is a field. -/
@[stacks 07NV]
theorem ringKrullDim_adicCompletion :
    ringKrullDim (AdicCompletion (maximalIdeal A) A) = ringKrullDim A := by
  let Â := AdicCompletion (maximalIdeal A) A
  let p := maximalIdeal A
  let P := maximalIdeal Â
  let _ : P.LiesOver p := ⟨by
    change p = Ideal.comap (algebraMap A Â) P
    exact (IsLocalRing.maximalIdeal_comap (algebraMap A Â)).symm⟩
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have hmap := map_maximalIdeal_adicCompletion A
  have hheight' : P.height = p.height := by
    rw [hmap, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at hheight
    exact hheight
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact congrArg _ hheight'

end RegularCompletion

section RegularCompletionRegular

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-- Stacks Tag `07NY`, forward direction: the completion of a regular local ring is a regular
local ring. -/
@[stacks 07NY "forward direction: `A` regular implies `Â` regular"]
instance isRegularLocalRing_adicCompletion :
    IsRegularLocalRing (AdicCompletion (maximalIdeal A) A) :=
  IsRegularLocalRing.of_map_maximalIdeal_eq_of_ringKrullDim_eq A _
    (map_maximalIdeal_adicCompletion A) (ringKrullDim_adicCompletion A).symm

end RegularCompletionRegular

#print axioms exists_sum_smul_of_mem_span_smul
#print axioms mem_smul_top_of_sub_mem_smul_of_smodEq
#print axioms IsAdicComplete.of_le
#print axioms isAdicComplete_of_finite
#print axioms isAdicComplete_map_of_finite
#print axioms isAdicComplete_map_self_of_finite
#print axioms isAdicComplete_quotient
#print axioms isAdicComplete_maximalIdeal_quotient
#print axioms isAdicComplete_span_singleton_of_finite
#print axioms isAdicComplete_map_span_singleton_of_finite
#print axioms isNoetherianRing_adicCompletion
#print axioms map_maximalIdeal_adicCompletion
#print axioms faithfullyFlat_adicCompletion
#print axioms ringKrullDim_adicCompletion
#print axioms isRegularLocalRing_adicCompletion

end Pcf.Stacks
