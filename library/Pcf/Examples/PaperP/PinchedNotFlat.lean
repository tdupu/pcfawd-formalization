/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedLine
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RingHom.Flat

/-!
# The pinched plane: `f` is not flat at `o`

For `paper-p.tex`, Example `ex:pinched`, closing remark: "the fibre of `f` over `ν(4, 1)` has
length `5`, while `f` has degree `4`, so `f` is not flat at `o`".

This file proves the conclusion **`f` is not flat at `o`** by a depth argument instead of the
length count (the length count is in `PinchedFibreLength`):

* `qIdeal = f*⁻¹(𝔪_o)`, the prime of `ν(4, 1)` (`mem_qIdeal_iff`);
* in `A = R_{ν(4,1)}`, the sequence `(w - 1, z² - 16)` is weakly regular
  (`isWeaklyRegular_A`): `A` is a domain and `z² - 16` is a nonzerodivisor modulo `w - 1`,
  using the conductor `z² - 4` (a unit of `A`);
* a flat local map preserves weakly regular sequences (`IsWeaklyRegular.of_flat`);
* but in `R_o` the images are `w² - 1 = (w - 1)(w + 1)` and `z⁴ - 16 ∈ 𝔪_o`, and `z⁴ - 16`
  kills the nonzero class of `z(w - 1)` in `R_o/(w - 1)` (the socle element of
  `PinchedLocalStructure.depth_at_o`).

Main statements: `localRingHom_not_flat` (algebraic) and `fScheme_stalkMap_not_flat`
(scheme-level: the stalk map of the actual `fScheme` at `o` is not flat).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedNotFlat

open AlgebraicGeometry CategoryTheory MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedAmbient
open Pcf.Examples.PaperP.PinchedLocalStructure Pcf.Examples.PaperP.PinchedLine
open RingTheory.Sequence
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k
local notation "Ao" => Localization.AtPrime (oIdeal k)

omit [CharZero k] in
theorem evalTwoOne_comp_squaringMap :
    (evalTwoOne k).comp (squaringMap k) = aeval ![(4 : k), 1] := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [evalTwoOne, squaringMap]; norm_num
  · simp [evalTwoOne, squaringMap]

/-- The prime of `ν(4, 1)`, as `f*⁻¹(𝔪_o)` (so that `f(o) = ν(4, 1)` holds by definition). -/
noncomputable def qIdeal : Ideal R := (oIdeal k).comap (fStar k)

instance qIdeal_isPrime : (qIdeal k).IsPrime := Ideal.comap_isPrime _ _

theorem mem_qIdeal_iff (h : R) : h ∈ qIdeal k ↔ aeval ![(4 : k), 1] (PinchedRing.val k h) = 0 := by
  change fStar k h ∈ oIdeal k ↔ _
  rw [mem_oIdeal_iff, val_fStar, ← evalTwoOne_comp_squaringMap]
  rfl

local notation "Aq" => Localization.AtPrime (qIdeal k)

/-- The local map `R_{ν(4,1)} → R_o` induced by `f*`. -/
noncomputable abbrev phi : Aq →+* Ao :=
  Localization.localRingHom (qIdeal k) (oIdeal k) (fStar k) rfl

/-- `z² - 16 ∈ R`. -/
noncomputable def zSqSub16 : R :=
  PinchedRing.mk k (X 0 ^ 2 - 16) (Subalgebra.sub_mem _ (z_sq_mem k)
    (by rw [mem_pinchedAlg_iff]; simp))

/-- `w + 1 ∈ R`. -/
noncomputable def wAddOne : R :=
  PinchedRing.mk k (X 1 + 1) (Subalgebra.add_mem _ (w_mem k) (Subalgebra.one_mem _))

theorem fStar_wSubOne : fStar k (wSubOne k) = wSubOne k * wAddOne k := by
  apply algebraMap_injective k
  change squaringMap k (X 1 - 1) = (X 1 - 1) * (X 1 + 1)
  simp [squaringMap]; ring

theorem fStar_zSqSub16_mem : fStar k (zSqSub16 k) ∈ oIdeal k := by
  rw [mem_oIdeal_iff, val_fStar]
  change evalTwoOne k (squaringMap k (X 0 ^ 2 - 16)) = 0
  rw [map_sub, map_pow, map_ofNat, map_sub, map_pow, map_ofNat]
  simp [evalTwoOne, squaringMap]; norm_num

theorem wAddOne_not_mem : wAddOne k ∉ oIdeal k := by
  rw [mem_oIdeal_iff]
  change ¬ evalTwoOne k (X 1 + 1) = 0
  norm_num [evalTwoOne]

theorem zSqSubFour_not_mem_qIdeal : zSqSubFour k ∉ qIdeal k := by
  rw [mem_qIdeal_iff]
  change ¬ aeval ![(4 : k), 1] (X 0 ^ 2 - 4) = 0
  simp; norm_num

theorem algebraMap_Aq_injective : Function.Injective (algebraMap R Aq) :=
  IsLocalization.injective _ (qIdeal k).primeCompl_le_nonZeroDivisors

/-! ### The weakly regular sequence `(w - 1, z² - 16)` in `A = R_{ν(4,1)}` -/

noncomputable abbrev yq : Aq := algebraMap R Aq (wSubOne k)
noncomputable abbrev xq : Aq := algebraMap R Aq (zSqSub16 k)

theorem planeRestr_ne_zero_of_not_mem {c : R} (hc : c ∉ qIdeal k) :
    planeRestr k (PinchedRing.val k c) ≠ 0 := by
  intro h
  apply hc
  rw [mem_qIdeal_iff, ← eval_planeRestr, h, Polynomial.eval_zero]

/-- `z² - 16` is a nonzerodivisor on `A/(w - 1)`. -/
theorem mem_span_of_mul_mem (a : Aq) (ha : xq k * a ∈ Ideal.span {yq k}) :
    a ∈ Ideal.span {yq k} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (qIdeal k).primeCompl a
  obtain ⟨⟨r', s'⟩, rfl⟩ := IsLocalization.mk'_surjective (qIdeal k).primeCompl b
  dsimp only at hb ⊢
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq] at hb
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (qIdeal k).primeCompl Aq).mp hb
  -- push to the line `w = 1`
  let ρ : R →+* Polynomial k := (planeRestr k).toRingHom.comp (algebraMap R S)
  have hρ : ∀ t : R, ρ t = planeRestr k (PinchedRing.val k t) := fun _ => rfl
  have hc' := congrArg ρ hc
  simp only [map_mul] at hc'
  have hw : ρ (wSubOne k) = 0 := by
    rw [hρ]; change planeRestr k (X 1 - 1) = 0; simp [planeRestr]
  have hx : ρ (zSqSub16 k) ≠ 0 := by
    rw [hρ]; change planeRestr k (X 0 ^ 2 - 16) ≠ 0
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    rw [map_sub, map_pow, map_ofNat] at this
    simp [planeRestr] at this
  rw [hw] at hc'
  simp only [zero_mul, mul_zero] at hc'
  have hr : planeRestr k (PinchedRing.val k r) = 0 := by
    rw [← hρ]
    rcases mul_eq_zero.mp hc'.symm with h | h
    · exact absurd h (by rw [hρ]; exact planeRestr_ne_zero_of_not_mem k c.2)
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by rw [hρ]; exact planeRestr_ne_zero_of_not_mem k s'.2)
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hx
    · exact h
  have hmem : PinchedRing.val k r ∈ Ideal.span {(X 1 - 1 : S)} := by
    rw [← planeLineIdeal_eq_span]; exact hr
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨t, ht⟩ := conductor k (zSqSubFour k) (zSqSubFour_mem_oIdeal k) q
  have key : r * zSqSubFour k = wSubOne k * t := by
    apply algebraMap_injective k
    rw [map_mul, map_mul, ht, algebraMap_pinched k r, ← hq]
    change q * (X 1 - 1) * PinchedRing.val k (zSqSubFour k) =
      (X 1 - 1) * (PinchedRing.val k (zSqSubFour k) * q)
    ring
  have hu : IsUnit (algebraMap R Aq (zSqSubFour k)) :=
    IsLocalization.map_units Aq (⟨zSqSubFour k, zSqSubFour_not_mem_qIdeal k⟩ :
      (qIdeal k).primeCompl)
  obtain ⟨u, hu'⟩ := hu
  have h1 : IsLocalization.mk' Aq r s * algebraMap R Aq (zSqSubFour k) =
      yq k * IsLocalization.mk' Aq t s := by
    rw [IsLocalization.mk'_eq_mul_mk'_one r, IsLocalization.mk'_eq_mul_mk'_one t,
      mul_right_comm, ← map_mul, key, map_mul]
    ring
  have : IsLocalization.mk' Aq r s =
      (IsLocalization.mk' Aq r s * algebraMap R Aq (zSqSubFour k)) * ↑u⁻¹ := by
    rw [← hu', mul_assoc, Units.mul_inv, mul_one]
  rw [this, h1, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem mem_smul_top_iff {B : Type*} [CommRing B] (r b : B) :
    b ∈ r • (⊤ : Submodule B B) ↔ b ∈ Ideal.span {r} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

theorem isWeaklyRegular_A : IsWeaklyRegular Aq [yq k, xq k] := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨fun a b h => ?_, ?_⟩
  · simp only [smul_eq_mul] at h
    have h0 : yq k ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap_Aq_injective k)).mpr (wSubOne_ne_zero k)
    exact mul_left_cancel₀ h0 h
  · rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro m hm
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      mem_smul_top_iff] at hm
    rw [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff]
    exact mem_span_of_mul_mem k a hm

/-! ### The contradiction in `R_o` -/

theorem phi_yq : phi k (yq k) = xo k * algebraMap R Ao (wAddOne k) := by
  rw [Localization.localRingHom_to_map, fStar_wSubOne, map_mul]

theorem phi_xq_mem : phi k (xq k) ∈ IsLocalRing.maximalIdeal Ao := by
  rw [Localization.localRingHom_to_map]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Ao (oIdeal k) _).mpr
    (fStar_zSqSub16_mem k)

theorem span_phi_yq : Ideal.span {phi k (yq k)} = Ideal.span {xo k} := by
  rw [phi_yq]
  apply Ideal.span_singleton_mul_right_unit
  exact IsLocalization.map_units Ao (⟨wAddOne k, wAddOne_not_mem k⟩ : (oIdeal k).primeCompl)

/-- **`f` is not flat at `o`** (algebraic form): the local map `R_{ν(4,1)} → R_o` induced by
`f*` is not flat. -/
theorem localRingHom_not_flat : ¬ (phi k).Flat := by
  intro hflat
  let _ : Algebra Aq Ao := (phi k).toAlgebra
  have : Module.Flat Aq Ao := hflat
  have h : IsWeaklyRegular Ao (List.map (algebraMap Aq Ao) [yq k, xq k]) :=
    (isWeaklyRegular_A k).of_flat
  simp only [List.map_cons, List.map_nil] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
  have hreg := h.2
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg
  have hc := hreg (Submodule.Quotient.mk (algebraMap R Ao (cElt k))) (by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      mem_smul_top_iff]
    change phi k (xq k) * _ ∈ Ideal.span {phi k (yq k)}
    rw [span_phi_yq]
    exact maximalIdeal_mul_cElt_mem k _ (phi_xq_mem k))
  rw [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff] at hc
  change _ ∈ Ideal.span {phi k (yq k)} at hc
  rw [span_phi_yq] at hc
  exact cElt_not_mem_span k hc

/-- **`f` is not flat at `o`** (scheme form): the stalk map of `fScheme` at `o` is not flat.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem fScheme_stalkMap_not_flat : ¬ ((fScheme k).stalkMap (oPoint k)).hom.Flat := by
  intro h
  apply localRingHom_not_flat k
  let e1 := Spec.stalkIso (CommRingCat.of R) (PrimeSpectrum.comap (fStar k) (oPoint k))
  let e2 := Spec.stalkIso (CommRingCat.of R) (oPoint k)
  have e : e1.hom ≫ CommRingCat.ofHom (phi k) ≫ e2.inv = (fScheme k).stalkMap (oPoint k) :=
    Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom (fStar k)) (oPoint k)
  rw [← e] at h
  have hL : CommRingCat.ofHom (phi k) =
      e1.inv ≫ (e1.hom ≫ CommRingCat.ofHom (phi k) ≫ e2.inv) ≫ e2.hom := by simp
  have hL' := congrArg CommRingCat.Hom.hom hL
  rw [CommRingCat.hom_ofHom] at hL'
  rw [hL', CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e1.inv))
    (RingHom.Flat.comp h
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e2.hom)))

#print axioms localRingHom_not_flat
#print axioms fScheme_stalkMap_not_flat

end Pcf.Examples.PaperP.PinchedNotFlat
