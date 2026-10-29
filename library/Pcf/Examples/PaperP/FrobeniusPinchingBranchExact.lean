/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingPCF
public import Pcf.Bounding.PointRamificationIdx

/-!
# `ex:frobenius-pinching`: the normalized branch divisors are exactly the two axes

`paper-p.tex`, Example `ex:frobenius-pinching`: "its normalized branch divisors are the
invariant axes". `FrobeniusPinchingPCF.weightedBranchPointSet_subset` gives one inclusion.
Here we prove that both axes are branch divisors: at the generic point of `V(X_i)` the stalk
map of `H(x,y) = (x², y²)` sends the maximal ideal `(X_i)` into `(X_i²) = (X_i)²`, so its
ramification index is not `1`, hence the weighted degree `δ = e · [κ:κ']_insep` is `> 1`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingBranchExact

open AlgebraicGeometry CategoryTheory MvPolynomial IsLocalRing
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators
open Pcf.Examples.PaperP.FrobeniusPinchingNormalization
open Pcf.Examples.PaperP.FrobeniusPinchingPCF

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- A local homomorphism into a Noetherian local domain that is not a field, sending the
maximal ideal into the square of the maximal ideal, has ramification index different from
`1` (Mathlib's length definition of `Ideal.ramificationIdx`). -/
theorem ramificationIdx_ne_one_of_map_le_sq {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B] [Algebra A B]
    (hne : maximalIdeal B ≠ ⊥)
    (hle : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B ^ 2) :
    (maximalIdeal B).ramificationIdx A ≠ 1 := by
  intro h
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  set m := maximalIdeal B
  let Sq := Localization.AtPrime m
  haveI : IsNoetherianRing Sq := IsLocalization.isNoetherianRing m.primeCompl Sq inferInstance
  have hunder : m.under A ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top')
  have hmSq : maximalIdeal Sq = m.map (algebraMap B Sq) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hle2 : maximalIdeal Sq ≤ maximalIdeal Sq ^ 2 := by
    calc maximalIdeal Sq = (m.under A).map (algebraMap A Sq) := h.symm
      _ ≤ (maximalIdeal A).map (algebraMap A Sq) := Ideal.map_mono hunder
      _ = ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B Sq) := by
        rw [IsScalarTower.algebraMap_eq A B Sq, Ideal.map_map]
      _ ≤ (m ^ 2).map (algebraMap B Sq) := Ideal.map_mono hle
      _ = maximalIdeal Sq ^ 2 := by rw [Ideal.map_pow, hmSq]
  have hidem : IsIdempotentElem (maximalIdeal Sq) := by
    apply le_antisymm
    · exact Ideal.mul_le_left
    · simpa [pow_two] using hle2
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing _).mp hidem with hb | ht
  · apply hne
    have hinj : Function.Injective (algebraMap B Sq) :=
      IsLocalization.injective Sq (Ideal.primeCompl_le_nonZeroDivisors m)
    rw [eq_bot_iff]
    intro b hb'
    have : algebraMap B Sq b ∈ maximalIdeal Sq := by
      rw [hmSq]; exact Ideal.mem_map_of_mem _ hb'
    rw [hb, Ideal.mem_bot, ← map_zero (algebraMap B Sq)] at this
    exact (hinj this).symm ▸ Ideal.zero_mem _
  · exact (maximalIdeal.isMaximal Sq).ne_top ht

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]

include p in
/-- `H` sends the axis prime `(X_i)` back to itself as an ideal: `square⁻¹ (X_i) = (X_i)`. -/
theorem comap_axis (i : Fin 2) :
    (Ideal.span {(X i : Plane k)}).comap (square k).toRingHom = Ideal.span {(X i : Plane k)} :=
  congrArg PrimeSpectrum.asIdeal (Hs_axisPt k p i)

theorem map_square_axis (i : Fin 2) :
    (Ideal.span {(X i : Plane k)}).map (square k).toRingHom = Ideal.span {(X i : Plane k)} ^ 2 := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
  congr 2
  fin_cases i <;> simp [square, x, y]

include p in
/-- **`H` is ramified along each axis**: at the generic point of `V(X_i)` the ramification
index of the actual stalk map of `H` is not `1`. -/
theorem Hs_ramificationIdx_axis_ne_one (i : Fin 2) :
    Pcf.schemeDivisorRamificationIdx (Hs k) ⟨axisPt k i, axisPt_coheight k i⟩ ≠ 1 := by
  let q : Spec (.of (Plane k)) := axisPt k i
  let f := CommRingCat.ofHom (square k).toRingHom
  let Q : Ideal (Plane k) := (q.asIdeal).comap (square k).toRingHom
  let ψ := Localization.localRingHom (PrimeSpectrum.comap f.hom q).asIdeal q.asIdeal f.hom rfl
  let e := Scheme.arrowStalkMapSpecIso f q
  let e₁ := (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
  let e₂ := (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv
  have hcomm : ψ.comp e₁.toRingHom = e₂.toRingHom.comp ((Hs k).stalkMap q).hom :=
    congrArg CommRingCat.Hom.hom e.hom.w
  have hidx := Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv ((Hs k).stalkMap q).hom ψ e₁ e₂
    hcomm
  unfold Pcf.schemeDivisorRamificationIdx
  change (letI := ((Hs k).stalkMap q).hom.toAlgebra;
    (maximalIdeal ((Spec (.of (Plane k))).presheaf.stalk q)).ramificationIdx
      ((Spec (.of (Plane k))).presheaf.stalk (Hs k q))) ≠ 1
  rw [hidx]
  letI : Algebra (Localization.AtPrime (PrimeSpectrum.comap f.hom q).asIdeal)
    (Localization.AtPrime q.asIdeal) := ψ.toAlgebra
  have hq : q.asIdeal = Ideal.span {(X i : Plane k)} := rfl
  have hQ : (PrimeSpectrum.comap f.hom q).asIdeal = Ideal.span {(X i : Plane k)} := by
    change Ideal.comap (square k).toRingHom q.asIdeal = _
    rw [hq]
    exact comap_axis k p i
  apply ramificationIdx_ne_one_of_map_le_sq
  · intro hb
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_eq_bot_iff_le_ker,
      RingHom.injective_iff_ker_eq_bot _ |>.mp (IsLocalization.injective _
        (Ideal.primeCompl_le_nonZeroDivisors q.asIdeal)), le_bot_iff, hq,
      Ideal.span_singleton_eq_bot] at hb
    exact X_ne_zero i hb
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map]
    have hψ : (algebraMap _ (Localization.AtPrime q.asIdeal)).comp
        (algebraMap (Plane k) (Localization.AtPrime (PrimeSpectrum.comap f.hom q).asIdeal)) =
        (algebraMap (Plane k) (Localization.AtPrime q.asIdeal)).comp (square k).toRingHom := by
      apply RingHom.ext
      intro a
      exact Localization.localRingHom_to_map _ _ _ rfl a
    rw [hψ, ← Ideal.map_map, hQ, map_square_axis, Ideal.map_pow, ← hq]

/-- The ramification index of the lift at `normIso⁻¹(axis)` equals that of `H` at the axis. -/
theorem lift_ramificationIdx_eq (z : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k p)))
    (hz : Order.coheight ((normIso k p).hom z.1) = 1) :
    Pcf.schemeDivisorRamificationIdx (lift k p) z =
      Pcf.schemeDivisorRamificationIdx (Hs k) ⟨(normIso k p).hom z.1, hz⟩ := by
  let a := (normIso k p).hom
  let b := (normIso k p).inv
  let y := Hs k (a z.1)
  let e₁ := (asIso (b.stalkMap y)).commRingCatIsoToRingEquiv
  let e₂ := (asIso (a.stalkMap z.1)).commRingCatIsoToRingEquiv.symm
  have hφ : (lift k p).stalkMap z.1 = b.stalkMap y ≫ (Hs k).stalkMap (a z.1) ≫ a.stalkMap z.1 := by
    unfold lift
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
    simp only [Category.assoc]
    rfl
  have hcomm : ((Hs k).stalkMap (a z.1)).hom.comp e₁.toRingHom =
      e₂.toRingHom.comp ((lift k p).stalkMap z.1).hom := by
    apply RingHom.ext
    intro r
    rw [hφ]
    change _ = e₂ ((a.stalkMap z.1).hom (((Hs k).stalkMap (a z.1)).hom ((b.stalkMap y).hom r)))
    change _ = (asIso (a.stalkMap z.1)).commRingCatIsoToRingEquiv.symm
      ((asIso (a.stalkMap z.1)).commRingCatIsoToRingEquiv _)
    rw [RingEquiv.symm_apply_apply]
    rfl
  exact Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv _ _ e₁ e₂ hcomm

/-- **Both axes are critical for the canonical lift**: `δ > 1` at `normIso⁻¹(V(X_i))`. -/
theorem delta_gt_one_of_axis (i : Fin 2) :
    1 < Pcf.schemeDivisorDelta (lift k p)
      ⟨(normIso k p).inv (axisPt k i),
        (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (normIso k p).inv).trans
          (axisPt_coheight k i)⟩ := by
  haveI := lift_finite k p
  set z : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k p)) :=
    ⟨(normIso k p).inv (axisPt k i),
      (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (normIso k p).inv).trans
        (axisPt_coheight k i)⟩
  have hz : (normIso k p).hom z.1 = axisPt k i := by
    change ((normIso k p).inv ≫ (normIso k p).hom) (axisPt k i) = _
    rw [Iso.inv_hom_id]
    rfl
  have hcoh : Order.coheight ((normIso k p).hom z.1) = 1 := by rw [hz]; exact axisPt_coheight k i
  have he : Pcf.schemeDivisorRamificationIdx (lift k p) z ≠ 1 := by
    rw [lift_ramificationIdx_eq k p z hcoh]
    have h := Hs_ramificationIdx_axis_ne_one k p i
    have hzz : (⟨(normIso k p).hom z.1, hcoh⟩ : Pcf.SchemeDivisorPoint (Spec (.of (Plane k)))) =
        ⟨axisPt k i, axisPt_coheight k i⟩ := Subtype.ext hz
    rw [hzz]
    exact h
  have hpos := Pcf.schemeDivisorDelta_pos_of_isFinite (lift k p) z
  unfold Pcf.schemeDivisorDelta at hpos ⊢
  set e := Pcf.schemeDivisorRamificationIdx (lift k p) z
  have key : ∀ n : ℕ, 0 < e * n → 1 < e * n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, mul_zero] at hn; exact absurd hn (lt_irrefl 0)
    have he0 : e ≠ 0 := fun h => by rw [h, zero_mul] at hn; exact lt_irrefl 0 hn
    have : 2 ≤ e := by omega
    nlinarith
  exact key _ hpos

/-- The two axis images are distinct points of `X`. -/
theorem axisImage_injective : Function.Injective (axisImage k p) := by
  have hy : y k ∈ ring k p := by
    apply Algebra.subset_adjoin
    right
    exact ⟨⟨0, (Fact.out : p.Prime).pos⟩, by simp⟩
  have hmem : ∀ i : Fin 2, (⟨y k, hy⟩ : ring k p) ∈ (axisImage k p i).asIdeal ↔
      (X 1 : Plane k) ∈ Ideal.span {(X i : Plane k)} := fun i => Iff.rfl
  have hne : axisImage k p 0 ≠ axisImage k p 1 := by
    intro h
    have h1 : (⟨y k, hy⟩ : ring k p) ∈ (axisImage k p 1).asIdeal :=
      (hmem 1).mpr (Ideal.mem_span_singleton_self _)
    have hI : (axisImage k p 0).asIdeal = (axisImage k p 1).asIdeal :=
      congrArg PrimeSpectrum.asIdeal h
    have h0 : (⟨y k, hy⟩ : ring k p) ∈ (axisImage k p 0).asIdeal := hI ▸ h1
    rw [hmem 0, Ideal.mem_span_singleton] at h0
    exact absurd ((MvPolynomial.X_dvd_X).mp h0) (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij hne
  · exact absurd hij.symm hne
  · rfl

/-- **`ex:frobenius-pinching`: the normalized weighted branch divisors of `f` are exactly the
two invariant axes** (generic points in `X` of the images of `V(x)` and `V(y)`), for
`2 ≠ 0` in `k`. -/
theorem weightedBranchPointSet_eq (h2 : (2 : k) ≠ 0) :
    Pcf.weightedBranchPointSet (descendedSchemeMap k p) = Set.range (axisImage k p) := by
  apply Set.Subset.antisymm (weightedBranchPointSet_subset k p h2)
  rintro _ ⟨i, rfl⟩
  have hF := (lift_eq_canonical k p).symm
  let d : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k p)) :=
    ⟨(normIso k p).inv (axisPt k i),
      (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (normIso k p).inv).trans
        (axisPt_coheight k i)⟩
  have hδ := delta_gt_one_of_axis k p i
  refine ⟨d.mapFiniteDominantNormal (Pcf.schemeGlobalNormalizationMorphism
    (descendedSchemeMap k p)), ⟨d, rfl, ?_⟩, ?_⟩
  · rw [hF]; exact hδ
  · have hi : (normIso k p).hom d.1 = axisPt k i := by
      change ((normIso k p).inv ≫ (normIso k p).hom) (axisPt k i) = _
      rw [Iso.inv_hom_id]
      rfl
    change Pcf.Palomar.normalizationMap (Xs k p)
      (Pcf.schemeGlobalNormalizationMorphism (descendedSchemeMap k p) d.1) = axisImage k p i
    rw [hF, ← Scheme.Hom.comp_apply, lift_comp_normalizationMap, Scheme.Hom.comp_apply,
      ← normIso_hom_nu, Scheme.Hom.comp_apply, hi]
    exact f_axisImage k p i

/-- The closed normalized weighted branch locus is the closure of the two axis points.

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem weightedBranchLocus_eq (h2 : (2 : k) ≠ 0) :
    Pcf.weightedBranchLocus (descendedSchemeMap k p) = closure (Set.range (axisImage k p)) := by
  rw [Pcf.weightedBranchLocus, weightedBranchPointSet_eq k p h2]

/-- The manuscript's hypotheses `char k = p ≥ 5`. -/
theorem weightedBranchPointSet_eq_of_charP [CharP k p] (hp : 5 ≤ p) :
    Pcf.weightedBranchPointSet (descendedSchemeMap k p) = Set.range (axisImage k p) :=
  weightedBranchPointSet_eq k p (two_ne_zero_of_charP k p (by omega))

#print axioms ramificationIdx_ne_one_of_map_le_sq
#print axioms Hs_ramificationIdx_axis_ne_one
#print axioms lift_ramificationIdx_eq
#print axioms delta_gt_one_of_axis
#print axioms axisImage_injective
#print axioms weightedBranchPointSet_eq
#print axioms weightedBranchLocus_eq
#print axioms weightedBranchPointSet_eq_of_charP

end Pcf.Examples.PaperP.FrobeniusPinchingBranchExact
