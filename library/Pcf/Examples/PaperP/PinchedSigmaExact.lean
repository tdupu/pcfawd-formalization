/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedSigma
public import Pcf.Examples.PaperP.PinchedRemark
public import Pcf.Examples.PaperP.PinchedNodeLocal
public import Pcf.Examples.PaperP.PinchedLyingOver

/-!
# `rem:pinched-unnormalized`: `Σ = {ν(0, 1), o}` exactly

For `paper-p.tex`, Remark `rem:pinched-unnormalized`: "`Σ`, which consists of `ν(0, 1)` and the
glued point `o`". Here `Σ = (B ∩ W_B) ∪ (B ∩ Sing X) ∪ Sing B` is the set from the proof of
`thm:bounding` / `prop:normal-unnormalized`, for `f` and the invariant divisor
`B = ν(V(w - 1))` (`r = 0`, `s = 1`, `F = f`): `W_B` is the union of the closures of the members
of `PC(f)` other than `B`.

Everything is a set of points of `X = Spec R`:

* `Bset = closure {η_B}`, `η_B = bPoint` the generic point of `B`;
* `WB = ⋃_{η ∈ PC(f), η ≠ η_B} closure {η}`, with `PC(f)` the weighted normalized
  post-critical point set `Pcf.weightedPostcriticalPointSet (fScheme k)`;
* `SingX = {x | 𝒪_{X,x} not regular}`;
* `Sing B` is computed on `B ≅ Spec R_B` (`PinchedLine.quotientLineEquiv`) and pushed into `X`
  along the closed embedding `ρ : R ↠ R_B` (`h ↦ h(z, 1)`).

Main results:

* `bset_inter_closure_axis_zero`: `B ∩ ν(V(z)) = {ν(0, 1)}` — the lying-over step: a prime of
  `R` containing `w - 1` and `z²` lies under a prime of `k[z, w]` containing `w - 1` and `z`,
  which is `(z, w - 1)` (`PinchedLyingOver.eq_ker_of_X_sub_C_mem`).
* `bset_inter_closure_axis_one`: `B ∩ ν(V(w)) = ∅`.
* `sigma_eq`: **`Σ = {ν(0, 1), o}`**.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedSigmaExact

open AlgebraicGeometry MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedAmbient
open Pcf.Examples.PaperP.PinchedBranchExact Pcf.Examples.PaperP.PinchedBoundingFailure
open Pcf.Examples.PaperP.PinchedLocalStructure Pcf.Examples.PaperP.PinchedLine
open Pcf.Examples.PaperP.PinchedSigma Pcf.Examples.PaperP.PinchedNodeFibre

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k
local notation "RB" => NodeRing k
local notation "Xs" => Spec (CommRingCat.of R)

/-- `B = closure {η_B}`. -/
def Bset : Set Xs := {x | (bPoint k).asIdeal ≤ x.asIdeal}

/-- `W_B`: the union of the closures of the members of `PC(f)` other than `B`. -/
def WB : Set Xs :=
  ⋃ η ∈ Pcf.weightedPostcriticalPointSet (fScheme k) \ {bPoint k}, closure {η}

/-- `Sing X`. -/
def SingX : Set Xs := {x | ¬ IsRegularLocalRing (Localization.AtPrime x.asIdeal)}

/-- `Sing B`, on `B ≅ Spec R_B`. -/
def SingB : Set (Spec (CommRingCat.of RB)) :=
  {y | ¬ IsRegularLocalRing (Localization.AtPrime y.asIdeal)}

/-- `Σ = (B ∩ W_B) ∪ (B ∩ Sing X) ∪ Sing B`, as a set of points of `X`. -/
def Sigma : Set Xs :=
  (Bset k ∩ WB k) ∪ (Bset k ∩ SingX k) ∪ (PrimeSpectrum.comap (lineRestr k)) '' SingB k

/-! ### Elements -/

theorem wSubOne_mem_bPoint : wSubOne k ∈ (bPoint k).asIdeal := by
  change planeRestr k (X 1 - 1) = 0
  simp [planeRestr]

/-- `w ∈ R`. -/
noncomputable def wElt : R := PinchedRing.mk k (X 1) (w_mem k)

theorem wElt_mem_axis_one : wElt k ∈ (axisImage k 1).asIdeal :=
  (mem_axisImage_iff k 1 _).mpr (Ideal.mem_span_singleton_self _)

theorem bElt_mem_axis_zero : bElt k ∈ (axisImage k 0).asIdeal :=
  (mem_axisImage_iff k 0 _).mpr
    (Ideal.mem_span_singleton'.mpr ⟨X 0, by change X 0 * X 0 = X 0 ^ 2; ring⟩)

theorem wSubOne_not_mem_axis (i : Fin 2) : wSubOne k ∉ (axisImage k i).asIdeal := by
  rw [mem_axisImage_iff, Ideal.mem_span_singleton']
  rintro ⟨q, hq⟩
  have := congrArg (aeval (fun _ : Fin 2 => (0 : k))) hq
  change aeval _ (q * X i) = aeval _ (X 1 - 1 : S) at this
  simp at this

theorem bPoint_ne_axisImage (i : Fin 2) : bPoint k ≠ axisImage k i := fun h =>
  wSubOne_not_mem_axis k i (h ▸ wSubOne_mem_bPoint k)

theorem bPoint_le_pointInX (a : k) : (bPoint k).asIdeal ≤ (pointInX k a).asIdeal := by
  intro h hh
  rw [bPoint_asIdeal, RingHom.mem_ker] at hh
  change lineRestr k h ∈ (pointQ k a).asIdeal
  rw [hh]
  exact zero_mem _

theorem pointInX_two : pointInX k 2 = oPoint k := by
  apply PrimeSpectrum.ext
  ext h
  rw [mem_pointInX_iff]
  exact (mem_oIdeal_iff k h).symm

/-! ### The pieces of `Σ` -/

theorem mem_WB_iff (x : Xs) :
    x ∈ WB k ↔ (axisImage k 0).asIdeal ≤ x.asIdeal ∨ (axisImage k 1).asIdeal ≤ x.asIdeal := by
  simp only [WB, weightedPostcriticalPointSet_eq, Set.mem_iUnion, Set.mem_sdiff, Set.mem_range,
    Set.mem_singleton_iff, exists_prop]
  constructor
  · rintro ⟨η, ⟨⟨i, rfl⟩, -⟩, hx⟩
    rw [← PrimeSpectrum.le_iff_mem_closure] at hx
    fin_cases i
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (h | h)
    · exact ⟨_, ⟨⟨0, rfl⟩, (bPoint_ne_axisImage k 0).symm⟩,
        (PrimeSpectrum.le_iff_mem_closure _ _).mp h⟩
    · exact ⟨_, ⟨⟨1, rfl⟩, (bPoint_ne_axisImage k 1).symm⟩,
        (PrimeSpectrum.le_iff_mem_closure _ _).mp h⟩

/-- **`B ∩ ν(V(z)) = {ν(0, 1)}`** (lying over). -/
theorem bset_inter_closure_axis_zero (x : Xs) :
    ((bPoint k).asIdeal ≤ x.asIdeal ∧ (axisImage k 0).asIdeal ≤ x.asIdeal) ↔
      x = pointInX k 0 := by
  constructor
  · rintro ⟨hB, hA⟩
    have hw := hB (wSubOne_mem_bPoint k)
    have hb := hA (bElt_mem_axis_zero k)
    have hker : (⊥ : Ideal S).under R ≤ x.asIdeal := by
      intro r hr
      have : r = 0 := algebraMap_injective k (by simpa using hr)
      rw [this]
      exact zero_mem _
    obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hker
    have hmem : ∀ h : R, h ∈ x.asIdeal → PinchedRing.val k h ∈ Q := fun h hh => by
      rw [← hQx] at hh
      exact hh
    have h0 : X 0 - C 0 ∈ Q := by
      have := hmem _ hb
      change (X 0 ^ 2 : S) ∈ Q at this
      simpa using hQ.mem_of_pow_mem 2 this
    have h1 : X 1 - C 1 ∈ Q := by
      have := hmem _ hw
      change (X 1 - 1 : S) ∈ Q at this
      simpa using this
    have hQe := PinchedLyingOver.eq_ker_of_X_sub_C_mem k 0 1 Q hQ.ne_top h0 h1
    apply PrimeSpectrum.ext
    ext h
    rw [mem_pointInX_iff, ← hQx, hQe]
    change aeval ![(0 : k), 1] (PinchedRing.val k h) = 0 ↔ _
    rfl
  · rintro rfl
    refine ⟨bPoint_le_pointInX k 0, ?_⟩
    intro h hh
    rw [mem_axisImage_iff, Ideal.mem_span_singleton'] at hh
    obtain ⟨q, hq⟩ := hh
    rw [mem_pointInX_iff, ← hq]
    simp

/-- **`B ∩ ν(V(w)) = ∅`**. -/
theorem bset_inter_closure_axis_one (x : Xs) :
    ¬ ((bPoint k).asIdeal ≤ x.asIdeal ∧ (axisImage k 1).asIdeal ≤ x.asIdeal) := by
  rintro ⟨hB, hA⟩
  have hw := hB (wSubOne_mem_bPoint k)
  have hv := hA (wElt_mem_axis_one k)
  have h1 : (1 : R) = wElt k - wSubOne k := by
    apply algebraMap_injective k
    change (1 : S) = X 1 - (X 1 - 1)
    ring
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (h1 ▸ sub_mem hv hw))

theorem mem_SingX_iff (x : Xs) : x ∈ SingX k ↔ x = oPoint k := by
  change ¬ _ ↔ _
  rw [isRegularLocalRing_iff_ne_o, not_not]
  exact ⟨fun h => PrimeSpectrum.ext h, fun h => h ▸ rfl⟩

theorem mem_SingB_iff (y : Spec (CommRingCat.of RB)) : y ∈ SingB k ↔ y = pointQ k 2 := by
  change ¬ _ ↔ _
  rw [PinchedNodeLocal.isRegularLocalRing_iff_ne_node, not_not]
  exact ⟨fun h => PrimeSpectrum.ext h, fun h => h ▸ rfl⟩

/-- **`Σ = {ν(0, 1), o}`** (`rem:pinched-unnormalized`).

`paper-p.tex` correspondence: Remark A.12 (`rem:pinched-unnormalized`). -/
theorem sigma_eq : Sigma k = {pointInX k 0, oPoint k} := by
  ext x
  simp only [Sigma, Set.mem_union, Set.mem_inter_iff, Set.mem_image, Set.mem_insert_iff,
    Set.mem_singleton_iff, mem_WB_iff, mem_SingX_iff]
  constructor
  · rintro ((⟨hB, h0 | h1⟩ | ⟨-, rfl⟩) | ⟨y, hy, rfl⟩)
    · exact Or.inl ((bset_inter_closure_axis_zero k x).mp ⟨hB, h0⟩)
    · exact absurd ⟨hB, h1⟩ (bset_inter_closure_axis_one k x)
    · exact Or.inr rfl
    · rw [mem_SingB_iff] at hy
      subst hy
      exact Or.inr (pointInX_two k)
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inl ⟨bPoint_le_pointInX k 0,
        Or.inl ((bset_inter_closure_axis_zero k _).mpr rfl).2⟩)
    · exact Or.inr ⟨pointQ k 2, (mem_SingB_iff k _).mpr rfl, pointInX_two k⟩

#print axioms bset_inter_closure_axis_zero
#print axioms bset_inter_closure_axis_one
#print axioms sigma_eq

end Pcf.Examples.PaperP.PinchedSigmaExact
