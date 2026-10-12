/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.Pi
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

namespace AdicCompletion

section ExactOfArtinRees

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type t} [AddCommGroup P] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- Adic completion preserves an injective map whenever its range satisfies the explicit
Artin–Rees equality.  This is the injectivity argument from Stacks Tag `06LD`, stated so that
it applies to uniform coordinatewise Artin–Rees equalities on arbitrary direct sums. -/
theorem map_injective_of_pow_inf_eq_pow_smul
    (hf : Function.Injective f) {k : ℕ}
    (hkn : ∀ n ≥ k,
      I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f =
        I ^ (n - k) • (I ^ k • (⊤ : Submodule R N) ⊓ LinearMap.range f)) :
    Function.Injective (AdicCompletion.map I f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  ext n
  obtain ⟨b, hb⟩ :=
    Submodule.Quotient.mk_surjective (I ^ (n + k) • ⊤ : Submodule R M) (x.val (n + k))
  have hfb : f b ∈ (I ^ (n + k) • ⊤ : Submodule R N) := by
    have hz := congrArg (fun z ↦ z.val (n + k)) hx
    simp only [AdicCompletion.map_val_apply, AdicCompletion.val_zero_apply] at hz
    rw [← Submodule.Quotient.mk_eq_zero]
    change (LinearMap.reduceModIdeal (I ^ (n + k)) f)
      (Submodule.Quotient.mk b) = 0
    rw [hb]
    exact hz
  have hbmem : b ∈ (I ^ n • ⊤ : Submodule R M) := by
    rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M),
      Submodule.map_smul'', Submodule.map_top]
    change f b ∈ I ^ n • LinearMap.range f
    apply (smul_mono_right _ inf_le_right :
      I ^ n • (I ^ k • ⊤ ⊓ LinearMap.range f) ≤ _)
    nth_rw 1 [show n = n + k - k by lia]
    rw [← hkn (n + k) (by lia)]
    exact ⟨hfb, ⟨b, rfl⟩⟩
  calc
    x.val n = AdicCompletion.transitionMap I M (show n ≤ n + k by lia) (x.val (n + k)) :=
      (x.property (show n ≤ n + k by lia)).symm
    _ = AdicCompletion.transitionMap I M (show n ≤ n + k by lia)
        (Submodule.Quotient.mk b) := congrArg _ hb.symm
    _ = Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) b := rfl
    _ = 0 := by rw [Submodule.Quotient.mk_eq_zero]; exact hbmem

/-- The correction step in adic exactness only uses the displayed Artin–Rees equality,
not finite generation itself.  Keeping that equality explicit lets us apply the argument to a
coordinatewise finite relation module. -/
private noncomputable def mapExactAuxDeltaOfPowInf
    {k n : ℕ}
    (hf : Function.Injective f)
    (hkn : ∀ n ≥ k,
      I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f =
        I ^ (n - k) • (I ^ k • (⊤ : Submodule R N) ⊓ LinearMap.range f))
    (x : ℕ → N)
    (hx : ∀ {m n}, m ≤ n →
      x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule R N)])
    {d : N} (hdmem : d ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N))
    {y yₙ : M} (hd : f y = x (k + n + 1) - d)
    (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N)) :
    {d : (I ^ n • ⊤ : Submodule R M) |
      f (yₙ + d) - x (k + n + 1) ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N)} := by
  have h : f (y - yₙ) ∈ (I ^ (k + n) • ⊤ : Submodule R N) := by
    simp only [map_sub, hd]
    convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) ∈
      I ^ (k + n) • (⊤ : Submodule R N)
    · abel
    · refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) hyₙ
      · rw [← Submodule.Quotient.eq]
        exact (hx (by lia)).symm
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hdmem
  have hincl : I ^ (k + n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f) ≤
      I ^ (k + n - k) • LinearMap.range f :=
    smul_mono_right _ inf_le_right
  have hyyₙ : y - yₙ ∈ (I ^ n • ⊤ : Submodule R M) := by
    convert_to y - yₙ ∈ (I ^ (k + n - k) • ⊤ : Submodule R M)
    · simp
    · rw [← Submodule.comap_map_eq_of_injective hf
          (I ^ (k + n - k) • ⊤ : Submodule R M)]
      rw [Submodule.map_smul'', Submodule.map_top]
      apply hincl
      rw [← hkn (k + n) (by lia)]
      exact ⟨h, ⟨y - yₙ, rfl⟩⟩
  exact ⟨⟨y - yₙ, hyyₙ⟩, by
    simpa [hd, Nat.succ_eq_add_one, Nat.add_assoc]⟩

/-- A compatible preimage sequence in the proof of adic exactness with an explicit
Artin–Rees constant. -/
private noncomputable def mapExactAuxOfPowInf
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {k : ℕ}
    (hkn : ∀ n ≥ k,
      I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f =
        I ^ (n - k) • (I ^ k • (⊤ : Submodule R N) ⊓ LinearMap.range f))
    (x : ℕ → N)
    (hx : ∀ {m n}, m ≤ n →
      x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule R N)])
    (hker : ∀ n : ℕ, g (x n) ∈ (I ^ n • ⊤ : Submodule R P)) :
    (n : ℕ) →
      {a : M | f a - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N)}
  | .zero =>
      let d := (h2 0).choose
      let y := (h2 0).choose_spec.choose
      have hdy : f y = x (k + 0) - d := (h2 0).choose_spec.choose_spec.right
      have hdmem : d ∈ (I ^ (k + 0) • ⊤ : Submodule R N) :=
        (h2 0).choose_spec.choose_spec.left
      ⟨y, by simpa [hdy] using hdmem⟩
  | .succ n =>
      let d := (h2 (n + 1)).choose
      let y := (h2 (n + 1)).choose_spec.choose
      have hdy : f y = x (k + (n + 1)) - d :=
        (h2 (n + 1)).choose_spec.choose_spec.right
      have hdmem := (h2 (n + 1)).choose_spec.choose_spec.left
      let ⟨yₙ, (hyₙ : f yₙ - x (k + n) ∈
          (I ^ (k + n) • ⊤ : Submodule R N))⟩ :=
        mapExactAuxOfPowInf hf hfg hg hkn x hx hker n
      let ⟨d, hd⟩ := mapExactAuxDeltaOfPowInf hf hkn x hx hdmem hdy hyₙ
      ⟨yₙ + d, hd⟩
where
  h1 (n : ℕ) : g (x (k + n)) ∈
      Submodule.map g (I ^ (k + n) • ⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
    exact hker (k + n)
  h2 (n : ℕ) : ∃ (d : N) (y : M),
      d ∈ (I ^ (k + n) • ⊤ : Submodule R N) ∧ f y = x (k + n) - d := by
    obtain ⟨d, hdmem, hd⟩ := h1 n
    obtain ⟨y, hdy⟩ := (hfg (x (k + n) - d)).mp (by simp [hd])
    exact ⟨d, y, hdmem, hdy⟩

/-- Adic completion preserves a short exact sequence whenever the middle submodule satisfies
the explicit Artin–Rees equality.  This is the proof of Mathlib's finite-module exactness with
the finiteness hypothesis replaced by the only consequence of it that the proof uses. -/
theorem map_exact_of_pow_inf_eq_pow_smul
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {k : ℕ}
    (hkn : ∀ n ≥ k,
      I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f =
        I ^ (n - k) • (I ^ k • (⊤ : Submodule R N) ⊓ LinearMap.range f)) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y ↦ ?_)
  · rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · intro hy
    choose b hb using fun n ↦
      Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R N) (y.val n)
    have hbCauchy : ∀ {m n}, m ≤ n →
        b m ≡ b n [SMOD (I ^ m • ⊤ : Submodule R N)] := by
      intro m n hmn
      rw [SModEq.def]
      calc
        Submodule.Quotient.mk (b m) = y.val m := hb m
        _ = AdicCompletion.transitionMap I N hmn (y.val n) := (y.property hmn).symm
        _ = AdicCompletion.transitionMap I N hmn
            (Submodule.Quotient.mk (b n)) := congrArg _ (hb n).symm
        _ = Submodule.Quotient.mk (b n) := rfl
    have hbker (n : ℕ) : g (b n) ∈ (I ^ n • ⊤ : Submodule R P) := by
      have hz := congrArg (fun x ↦ x.val n) (LinearMap.mem_ker.mp hy)
      simp only [AdicCompletion.map_val_apply, AdicCompletion.val_zero_apply] at hz
      rw [← hb n, LinearMap.reduceModIdeal_apply] at hz
      rw [← Submodule.Quotient.mk_eq_zero]
      exact hz
    let a := mapExactAuxOfPowInf hf hfg hg hkn b hbCauchy hbker
    have haSucc (n : ℕ) :
        (a n : M) ≡ (a (n + 1) : M) [SMOD (I ^ n • ⊤ : Submodule R M)] := by
      simp [a, mapExactAuxOfPowInf, SModEq]
    have haCauchy : ∀ {m n}, m ≤ n →
        (a m : M) ≡ (a n : M) [SMOD (I ^ m • ⊤ : Submodule R M)] := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => rfl
      | succ n hmn ih =>
          exact ih.trans ((haSucc n).mono
            (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)))
    let z : AdicCompletion I M :=
      ⟨fun n ↦ Submodule.Quotient.mk (a n : M), fun hmn ↦ by
        change Submodule.Quotient.mk (a _ : M) = Submodule.Quotient.mk (a _ : M)
        exact (haCauchy hmn).symm⟩
    refine ⟨z, ?_⟩
    ext n
    change Submodule.Quotient.mk (f (a n : M)) = y.val n
    rw [← hb n, Submodule.Quotient.eq]
    have hle : (I ^ (k + n) • ⊤ : Submodule R N) ≤
        (I ^ n • ⊤ : Submodule R N) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))
    have hb' := (hbCauchy (show n ≤ k + n by lia)).symm
    rw [SModEq.sub_mem] at hb'
    convert Submodule.add_mem _ (hle (a n).property) hb' using 1
    all_goals abel

end ExactOfArtinRees

end AdicCompletion

namespace Finsupp

/-- Transpose an arbitrary direct sum past a finite product. -/
noncomputable def finsuppPiLEquiv
    {R : Type u} [CommRing R] (ι : Type v) (κ : Type w) [Finite κ] :
    (ι →₀ (κ → R)) ≃ₗ[R] κ → (ι →₀ R) :=
  Finsupp.mapRange.linearEquiv (Finsupp.linearEquivFunOnFinite R R κ).symm ≪≫ₗ
    (Finsupp.curryLinearEquiv R).symm ≪≫ₗ
    Finsupp.domLCongr (Equiv.prodComm ι κ) ≪≫ₗ
    Finsupp.curryLinearEquiv R ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R (ι →₀ R) κ

@[simp]
theorem finsuppPiLEquiv_apply
    {R : Type u} [CommRing R] (ι : Type v) (κ : Type w) [Finite κ]
    (x : ι →₀ (κ → R)) (j : κ) (i : ι) :
    (Finsupp.finsuppPiLEquiv (R := R) ι κ).toLinearMap x j i = x i j := by
  rfl

@[simp]
theorem finsuppPiLEquiv_symm_apply
    {R : Type u} [CommRing R] (ι : Type v) (κ : Type w) [Finite κ]
    (x : κ → (ι →₀ R)) (j : κ) (i : ι) :
    (Finsupp.finsuppPiLEquiv (R := R) ι κ).symm.toLinearMap x i j = x j i := by
  rw [← Finsupp.finsuppPiLEquiv_apply ι κ]
  exact congrArg (fun z : κ → (ι →₀ R) ↦ z j i)
    ((Finsupp.finsuppPiLEquiv (R := R) ι κ).apply_symm_apply x)

/-- Multiplication by an ideal commutes with a direct sum of copies of a submodule. -/
theorem ideal_smul_submodule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) (S : Submodule R M) (ι : Type w) :
    J • Finsupp.submodule (fun _ : ι ↦ S) =
      Finsupp.submodule (fun _ : ι ↦ J • S) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr x hx
    rw [Finsupp.mem_submodule_iff] at hx ⊢
    intro i
    exact Submodule.smul_mem_smul hr (hx i)
  · intro x hx
    rw [← Finsupp.sum_single x]
    apply Submodule.sum_mem
    intro i _
    have hxi : x i ∈ J • S := hx i
    refine Submodule.smul_induction_on hxi ?_ ?_
    · intro r hr y hy
      rw [← Finsupp.smul_single]
      exact Submodule.smul_mem_smul hr (by
        rw [Finsupp.mem_submodule_iff]
        intro j
        by_cases hji : j = i
        · subst j
          simpa using hy
        · simp [hji])
    · intro y z hy hz
      simpa only [Finsupp.single_add] using Submodule.add_mem _ hy hz

/-- Intersections of coordinatewise submodules are computed coordinatewise. -/
@[simp]
theorem submodule_inf
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type w} (S T : ι → Submodule R M) :
    Finsupp.submodule S ⊓ Finsupp.submodule T =
      Finsupp.submodule (fun i ↦ S i ⊓ T i) := by
  ext x
  simp only [Submodule.mem_inf, Finsupp.mem_submodule_iff]
  aesop

/-- The Artin–Rees equality for a finite submodule remains uniform after taking an arbitrary
direct sum of copies.  This is the uniform shift used in Stacks Tag `06LD`. -/
theorem exists_pow_inf_eq_pow_smul_submodule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (S : Submodule R M) (ι : Type w) :
    ∃ k : ℕ, ∀ n ≥ k,
      I ^ n • (⊤ : Submodule R (ι →₀ M)) ⊓
          Finsupp.submodule (fun _ : ι ↦ S) =
        I ^ (n - k) •
          (I ^ k • (⊤ : Submodule R (ι →₀ M)) ⊓
            Finsupp.submodule (fun _ : ι ↦ S)) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I S
  refine ⟨k, fun n hn ↦ ?_⟩
  calc
    I ^ n • (⊤ : Submodule R (ι →₀ M)) ⊓
          Finsupp.submodule (fun _ : ι ↦ S) =
        Finsupp.submodule (fun _ : ι ↦ I ^ n • (⊤ : Submodule R M) ⊓ S) := by
      rw [← Finsupp.submodule_top (R := R) (M := M) (α := ι),
        Finsupp.ideal_smul_submodule, Finsupp.submodule_inf]
    _ = Finsupp.submodule (fun _ : ι ↦
          I ^ (n - k) • (I ^ k • (⊤ : Submodule R M) ⊓ S)) := by
      rw [hk n hn]
    _ = I ^ (n - k) •
          (I ^ k • (⊤ : Submodule R (ι →₀ M)) ⊓
            Finsupp.submodule (fun _ : ι ↦ S)) := by
      rw [← Finsupp.submodule_top (R := R) (M := M) (α := ι),
        Finsupp.ideal_smul_submodule, Finsupp.submodule_inf,
        Finsupp.ideal_smul_submodule]

end Finsupp

namespace Fintype

/-- Apply a finite matrix of coefficients to a tuple with values in an arbitrary module. -/
noncomputable def linearCombinationPi
    {R : Type u} [CommRing R] {κ : Type v} [Fintype κ]
    {η : Type w} (a : κ → η → R)
    (M : Type t) [AddCommGroup M] [Module R M] :
    (κ → M) →ₗ[R] η → M :=
  LinearMap.pi (fun i ↦ ∑ j, a j i • LinearMap.proj j)

@[simp]
theorem linearCombinationPi_apply
    {R : Type u} [CommRing R] {κ : Type v} [Fintype κ]
    {η : Type w} (a : κ → η → R)
    (M : Type t) [AddCommGroup M] [Module R M]
    (x : κ → M) (i : η) :
    Fintype.linearCombinationPi a M x i = ∑ j, a j i • x j := by
  simp [Fintype.linearCombinationPi]

end Fintype

namespace Finsupp

/-- Transposition intertwines a coordinatewise finite matrix with the same matrix acting on
the finite tuple of direct sums. -/
theorem finsuppPiLEquiv_mapRange_linearCombination
    {R : Type u} [CommRing R] {κ : Type v} [Fintype κ]
    {η : Type w} [Finite η] (a : κ → η → R) (ι : Type t)
    (x : ι →₀ (κ → R)) :
    (Finsupp.finsuppPiLEquiv (R := R) ι η).toLinearMap
        (Finsupp.mapRange.linearMap (Fintype.linearCombination R a) x) =
      Fintype.linearCombinationPi a (ι →₀ R)
        ((Finsupp.finsuppPiLEquiv (R := R) ι κ).toLinearMap x) := by
  ext i j
  rw [Finsupp.finsuppPiLEquiv_apply, Fintype.linearCombinationPi_apply]
  change (Fintype.linearCombination R a) (x j) i = _
  rw [Fintype.linearCombination_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  change (∑ k, x j k * a k i) =
    (Finsupp.applyAddHom j) (∑ k, a k i •
      (Finsupp.finsuppPiLEquiv (R := R) ι κ).toLinearMap x k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end Finsupp

namespace AdicCompletion

/-- The finite-matrix/transpose square remains natural after adic completion. -/
theorem piEquivFin_map_mapRange_linearCombination
    {R : Type u} [CommRing R] (I : Ideal R) (ι : Type v)
    {k l : ℕ} (a : Fin k → Fin l → R)
    (z : AdicCompletion I (ι →₀ (Fin k → R))) :
    AdicCompletion.piEquivOfFintype I (fun _ : Fin l ↦ ι →₀ R)
        (AdicCompletion.map I
          (Finsupp.finsuppPiLEquiv (R := R) ι (Fin l)).toLinearMap
          (AdicCompletion.map I
            (Finsupp.mapRange.linearMap (Fintype.linearCombination R a)) z)) =
      fun i ↦ ∑ j, a j i •
        AdicCompletion.piEquivOfFintype I (fun _ : Fin k ↦ ι →₀ R)
          (AdicCompletion.map I
            (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap z) j := by
  funext i
  simp only [AdicCompletion.piEquivOfFintype_apply]
  change AdicCompletion.map I (LinearMap.proj i)
      (AdicCompletion.map I
        (Finsupp.finsuppPiLEquiv (R := R) ι (Fin l)).toLinearMap
        (AdicCompletion.map I
          (Finsupp.mapRange.linearMap (Fintype.linearCombination R a)) z)) = _
  simp only [AdicCompletion.map_comp_apply]
  have hraw :
      LinearMap.proj i ∘ₗ
          (Finsupp.finsuppPiLEquiv (R := R) ι (Fin l)).toLinearMap ∘ₗ
          Finsupp.mapRange.linearMap (Fintype.linearCombination R a) =
        ∑ j, a j i •
          (LinearMap.proj j ∘ₗ
            (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    simpa only [Fintype.linearCombinationPi_apply, LinearMap.proj_apply] using
      congrArg (fun y : Fin l → (ι →₀ R) ↦ y i)
        (Finsupp.finsuppPiLEquiv_mapRange_linearCombination a ι x)
  rw [hraw]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact (AdicCompletion.map_comp_apply (I := I)
    (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap
    (LinearMap.proj j) z).symm

/-- Scalar-valued form of `piEquivFin_map_mapRange_linearCombination`. -/
theorem map_mapRange_linearCombination_eq_sum
    {R : Type u} [CommRing R] (I : Ideal R) (ι : Type v)
    {k : ℕ} (c : Fin k → R)
    (z : AdicCompletion I (ι →₀ (Fin k → R))) :
    AdicCompletion.map I
        (Finsupp.mapRange.linearMap (Fintype.linearCombination R c)) z =
      ∑ j, c j •
        AdicCompletion.piEquivOfFintype I (fun _ : Fin k ↦ ι →₀ R)
          (AdicCompletion.map I
            (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap z) j := by
  simp only [AdicCompletion.piEquivOfFintype_apply]
  have hraw :
      Finsupp.mapRange.linearMap (α := ι) (Fintype.linearCombination R c) =
        ∑ j, c j •
          (LinearMap.proj j ∘ₗ
            (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap) := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    change (Fintype.linearCombination R c) (x i) =
      (Finsupp.applyAddHom i) (∑ j, c j •
        (LinearMap.proj (R := R) j :
          (Fin k → (ι →₀ R)) →ₗ[R] (ι →₀ R))
          ((Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap x))
    rw [Fintype.linearCombination_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change x i j * c j = c j *
      (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap x j i
    rw [Finsupp.finsuppPiLEquiv_apply]
    exact mul_comm _ _
  rw [hraw]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact (AdicCompletion.map_comp_apply (I := I)
    (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap
    (LinearMap.proj j) z).symm

/-- Completion preserves a coordinatewise short exact sequence obtained by taking an
arbitrary direct sum of copies of a short exact sequence with finite middle term.  This is
the exactness form of the Artin–Rees argument in Stacks Tag `06LD`. -/
theorem mapRange_exact_of_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {P : Type t} [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (ι : Type*) :
    Function.Exact
      (AdicCompletion.map I (Finsupp.mapRange.linearMap (α := ι) f))
      (AdicCompletion.map I (Finsupp.mapRange.linearMap (α := ι) g)) := by
  have hf' : Function.Injective (Finsupp.mapRange.linearMap (α := ι) f) := by
    intro x y hxy
    ext i
    apply hf
    exact congrArg (fun z ↦ z i) hxy
  have hg' : Function.Surjective (Finsupp.mapRange.linearMap (α := ι) g) := by
    intro y
    obtain ⟨x, hx⟩ := Finsupp.mapRange_surjective g g.map_zero hg y
    exact ⟨x, hx⟩
  have hfg' : Function.Exact
      (Finsupp.mapRange.linearMap (α := ι) f)
      (Finsupp.mapRange.linearMap (α := ι) g) := by
    rw [LinearMap.exact_iff, Finsupp.ker_mapRange,
      Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.mpr hf),
      hfg.linearMap_ker_eq]
  obtain ⟨k, hk⟩ :=
    Finsupp.exists_pow_inf_eq_pow_smul_submodule I (LinearMap.range f) ι
  apply AdicCompletion.map_exact_of_pow_inf_eq_pow_smul hf' hfg' hg'
  simpa only [Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.mpr hf)] using hk

/-- Completion preserves injectivity after taking an arbitrary direct sum of copies of an
injective map with finite target.  This is the universal injectivity form of Stacks Tag
`06LD`. -/
theorem mapRange_injective_of_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {f : M →ₗ[R] N} (hf : Function.Injective f) (ι : Type*) :
    Function.Injective
      (AdicCompletion.map I (Finsupp.mapRange.linearMap (α := ι) f)) := by
  have hf' : Function.Injective (Finsupp.mapRange.linearMap (α := ι) f) := by
    intro x y hxy
    ext i
    apply hf
    exact congrArg (fun z ↦ z i) hxy
  obtain ⟨k, hk⟩ :=
    Finsupp.exists_pow_inf_eq_pow_smul_submodule I (LinearMap.range f) ι
  apply AdicCompletion.map_injective_of_pow_inf_eq_pow_smul hf'
  simpa only [Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.mpr hf)] using hk

/-- A relation in the completion of an arbitrary direct sum of copies of a finite module lifts
to the completion of the coordinatewise kernel.  The use of the range restriction, followed by
`mapRange_injective_of_finite`, is the finite-presentation relation step in Stacks Tag `06LD`. -/
theorem exists_mapRange_ker_preimage_of_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (q : N →ₗ[R] P) (ι : Type t) (x : AdicCompletion I (ι →₀ N))
    (hx : AdicCompletion.map I (Finsupp.mapRange.linearMap (α := ι) q) x = 0) :
    ∃ y : AdicCompletion I (ι →₀ LinearMap.ker q),
      AdicCompletion.map I
        (Finsupp.mapRange.linearMap (α := ι) (LinearMap.ker q).subtype) y = x := by
  have hshort : Function.Exact (LinearMap.ker q).subtype q.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hsurj : Function.Surjective q.rangeRestrict :=
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict q)
  have hexact := AdicCompletion.mapRange_exact_of_finite
    (I := I) (f := (LinearMap.ker q).subtype) (g := q.rangeRestrict)
    (LinearMap.ker q).subtype_injective hshort hsurj ι
  have hincl : Function.Injective
      (AdicCompletion.map I
        (Finsupp.mapRange.linearMap (α := ι) (LinearMap.range q).subtype)) :=
    AdicCompletion.mapRange_injective_of_finite
      (I := I) (LinearMap.range q).subtype_injective ι
  have hzero : AdicCompletion.map I
      (Finsupp.mapRange.linearMap (α := ι) q.rangeRestrict) x = 0 := by
    apply (injective_iff_map_eq_zero _).mp hincl
    rw [AdicCompletion.map_comp_apply]
    have hcomp :
        Finsupp.mapRange.linearMap (α := ι) (LinearMap.range q).subtype ∘ₗ
            Finsupp.mapRange.linearMap (α := ι) q.rangeRestrict =
          Finsupp.mapRange.linearMap (α := ι) q := by
      rw [← Finsupp.mapRange.linearMap_comp]
      rfl
    rw [hcomp, hx]
  exact (hexact x).mp hzero

/-- The adic completion of an arbitrary free module over a Noetherian ring is flat.  This is
Stacks Tag `06LE`, using the finite-presentation relation argument of Tag `06LD`. -/
theorem finsupp_flat_of_isNoetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (ι : Type v) :
    Module.Flat R (AdicCompletion I (ι →₀ R)) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l c x hx
  let q : (Fin l → R) →ₗ[R] R := Fintype.linearCombination R c
  let e := Finsupp.finsuppPiLEquiv (R := R) ι (Fin l)
  let xPi : AdicCompletion I (Fin l → (ι →₀ R)) :=
    (AdicCompletion.piEquivOfFintype I (fun _ : Fin l ↦ ι →₀ R)).symm x
  let xSum : AdicCompletion I (ι →₀ (Fin l → R)) :=
    AdicCompletion.map I e.symm.toLinearMap xPi
  have he : AdicCompletion.map I e.toLinearMap xSum = xPi := by
    dsimp only [xSum]
    rw [AdicCompletion.map_comp_apply]
    rw [e.comp_symm, AdicCompletion.map_id]
    rfl
  have hxSum : AdicCompletion.map I
      (Finsupp.mapRange.linearMap (α := ι) q) xSum = 0 := by
    rw [show q = Fintype.linearCombination R c from rfl]
    rw [AdicCompletion.map_mapRange_linearCombination_eq_sum]
    rw [he]
    simpa only [xPi, LinearEquiv.apply_symm_apply] using hx
  obtain ⟨yKer, hyKer⟩ :=
    AdicCompletion.exists_mapRange_ker_preimage_of_finite q ι xSum hxSum
  let K := LinearMap.ker q
  let _ : Module.Finite R K := inferInstance
  have hfg : (⊤ : Submodule R K).FG := Module.Finite.fg_top
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  let a : (Fin k → R) →ₗ[R] K := Fintype.linearCombination R g
  have ha : Function.Surjective a := by
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination R g).mp hg
  have haSum : Function.Surjective
      (Finsupp.mapRange.linearMap (α := ι) a) := by
    intro z
    obtain ⟨w, hw⟩ := Finsupp.mapRange_surjective a a.map_zero ha z
    exact ⟨w, hw⟩
  obtain ⟨z, hz⟩ := AdicCompletion.map_surjective I haSum yKer
  let coeff : Fin k → Fin l → R := fun j ↦ (g j : Fin l → R)
  have hcoeff : Fintype.linearCombination R coeff = K.subtype.comp a := by
    apply LinearMap.ext
    intro r
    change (∑ j, r j • (g j : Fin l → R)) =
      ((∑ j, r j • g j : K) : Fin l → R)
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hxSum' : AdicCompletion.map I
      (Finsupp.mapRange.linearMap (α := ι)
        (Fintype.linearCombination R coeff)) z = xSum := by
    calc
      AdicCompletion.map I
          (Finsupp.mapRange.linearMap (α := ι)
            (Fintype.linearCombination R coeff)) z =
          AdicCompletion.map I
            (Finsupp.mapRange.linearMap (α := ι) K.subtype ∘ₗ
              Finsupp.mapRange.linearMap (α := ι) a) z := by
            rw [hcoeff, ← Finsupp.mapRange.linearMap_comp]
      _ = AdicCompletion.map I
            (Finsupp.mapRange.linearMap (α := ι) K.subtype)
            (AdicCompletion.map I
              (Finsupp.mapRange.linearMap (α := ι) a) z) :=
          (AdicCompletion.map_comp_apply (I := I) _ _ z).symm
      _ = AdicCompletion.map I
            (Finsupp.mapRange.linearMap (α := ι) K.subtype) yKer := by
          rw [hz]
      _ = xSum := hyKer
  let y : Fin k → AdicCompletion I (ι →₀ R) :=
    AdicCompletion.piEquivOfFintype I (fun _ : Fin k ↦ ι →₀ R)
      (AdicCompletion.map I
        (Finsupp.finsuppPiLEquiv (R := R) ι (Fin k)).toLinearMap z)
  refine ⟨k, (fun i j ↦ coeff j i), y, ?_, ?_⟩
  · intro i
    have hnat := AdicCompletion.piEquivFin_map_mapRange_linearCombination
      I ι coeff z
    rw [hxSum', he] at hnat
    exact congrFun (by simpa only [xPi, y, LinearEquiv.apply_symm_apply] using hnat) i
  · intro j
    have hj : q (g j : Fin l → R) = 0 := (g j).property
    simpa only [q, Fintype.linearCombination_apply, coeff, smul_eq_mul, mul_comm] using hj

end AdicCompletion

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
#print axioms AdicCompletion.map_injective_of_pow_inf_eq_pow_smul
#print axioms AdicCompletion.map_exact_of_pow_inf_eq_pow_smul
#print axioms Finsupp.finsuppPiLEquiv
#print axioms Finsupp.finsuppPiLEquiv_apply
#print axioms Finsupp.finsuppPiLEquiv_symm_apply
#print axioms Fintype.linearCombinationPi
#print axioms Fintype.linearCombinationPi_apply
#print axioms Finsupp.finsuppPiLEquiv_mapRange_linearCombination
#print axioms Finsupp.ideal_smul_submodule
#print axioms Finsupp.submodule_inf
#print axioms Finsupp.exists_pow_inf_eq_pow_smul_submodule
#print axioms AdicCompletion.mapRange_exact_of_finite
#print axioms AdicCompletion.mapRange_injective_of_finite
#print axioms AdicCompletion.piEquivFin_map_mapRange_linearCombination
#print axioms AdicCompletion.map_mapRange_linearCombination_eq_sum
#print axioms AdicCompletion.exists_mapRange_ker_preimage_of_finite
#print axioms AdicCompletion.finsupp_flat_of_isNoetherian
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
