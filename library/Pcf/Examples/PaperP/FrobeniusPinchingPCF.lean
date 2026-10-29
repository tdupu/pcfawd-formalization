/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingNormalization
public import Pcf.Examples.PaperP.FrobeniusLineWeightedBranch
public import Pcf.Bounding.PaperPIteration
public import Pcf.Bounding.SchemeGenericSeparabilityMap
public import Pcf.Bounding.SchemeWeightedCriticalFinite

/-!
# `ex:frobenius-pinching`: weighted branch locus and PCF

For `p` an odd prime and `char k = p`, the descended map `f` on the pinched surface
`X = Spec(k[x^p] + y k[x,y])` is generically separable, every normalized weighted
branch divisor of `f` lies over one of the two axes of `A²`, these two points of `X`
are fixed by `f`, and hence `f` satisfies the paper's separable normalized PCF predicate.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingPCF

open AlgebraicGeometry CategoryTheory MvPolynomial
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators
open Pcf.Examples.PaperP.FrobeniusPinchingNormalization
open Pcf.Examples.PaperP.CoordinateSquareEtale (sqScheme sqScheme_stalk_formallyEtale sq)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k]

/-! ### `H` as a composite of one-coordinate squarings -/

theorem square_eq_comp : square k = (sq k (Fin 2) 0).comp (sq k (Fin 2) 1) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [square, x, CoordinateSquareEtale.sq]
  · simp [square, y, CoordinateSquareEtale.sq]

theorem Hs_eq : Hs k = sqScheme k (Fin 2) 0 ≫ sqScheme k (Fin 2) 1 := by
  unfold Hs sqScheme
  rw [← Spec.map_comp, square_eq_comp]
  rfl

/-- `H` is formally étale at every point off the two axes. -/
theorem Hs_stalk_formallyEtale (h2 : (2 : k) ≠ 0) (q : Spec (.of (Plane k)))
    (hx : (X 0 : Plane k) ∉ q.asIdeal) (hy : (X 1 : Plane k) ∉ q.asIdeal) :
    ((Hs k).stalkMap q).hom.FormallyEtale := by
  rw [Hs_eq, Scheme.Hom.stalkMap_comp]
  have h0 := sqScheme_stalk_formallyEtale k (Fin 2) 0 h2 q hx
  have h1 : ((sqScheme k (Fin 2) 1).stalkMap (sqScheme k (Fin 2) 0 q)).hom.FormallyEtale := by
    apply sqScheme_stalk_formallyEtale k (Fin 2) 1 h2
    change (X 1 : Plane k) ∉ (q.asIdeal).comap (sq k (Fin 2) 0).toRingHom
    rw [Ideal.mem_comap]
    change sq k (Fin 2) 0 (X 1) ∉ q.asIdeal
    rw [CoordinateSquareEtale.sq_X_ne k (Fin 2) 0 (by decide)]
    exact hy
  exact RingHom.FormallyEtale.comp h1 h0


/-! ### Points on the axes -/

/-- The generic point of the axis `V(X_i)` of `A²`. -/
noncomputable def axisPt (i : Fin 2) : Spec (.of (Plane k)) :=
  ⟨Ideal.span {(X i : Plane k)},
    (Ideal.span_singleton_prime (X_ne_zero i)).mpr MvPolynomial.X_prime⟩

/-- A codimension-one point of `A²` containing `X_i` is the generic point of `V(X_i)`. -/
theorem eq_axisPt (q : Spec (.of (Plane k))) (hq : Order.coheight q = 1) (i : Fin 2)
    (hi : (X i : Plane k) ∈ q.asIdeal) : q = axisPt k i := by
  have hh : q.asIdeal.height = 1 := by
    rw [AlgebraicGeometry.idealHeight_eq_coheight]
    exact hq
  let P : Ideal (Plane k) := Ideal.span {(X i : Plane k)}
  haveI : P.IsPrime := (axisPt k i).2
  have hPq : P ≤ q.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hi
  by_contra hne
  have hlt : P < q.asIdeal := lt_of_le_of_ne hPq (fun h => hne (PrimeSpectrum.ext h.symm))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hbot : (⊥ : Ideal (Plane k)) < P := by
    rw [bot_lt_iff_ne_bot]
    intro h
    rw [Ideal.span_singleton_eq_bot] at h
    exact X_ne_zero i h
  have h0 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  rw [Ideal.height_bot, zero_add] at h0
  rw [hh] at h1
  have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h0 1).trans h1
  exact absurd this (by norm_num)

/-! ### Stalks of the lift -/

theorem iso_stalk_formallyEtale {X Y : Scheme} (e : X ⟶ Y) [IsIso e] (x : X) :
    (e.stalkMap x).hom.FormallyEtale :=
  Pcf.ringEquiv_formallyEtale (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv

variable (p : ℕ) [Fact p.Prime]

theorem lift_stalk_formallyEtale (h2 : (2 : k) ≠ 0) (z : Pcf.Palomar.normalization (Xs k p))
    (hx : (X 0 : Plane k) ∉ ((normIso k p).hom z).asIdeal)
    (hy : (X 1 : Plane k) ∉ ((normIso k p).hom z).asIdeal) :
    ((lift k p).stalkMap z).hom.FormallyEtale := by
  unfold lift
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
  refine RingHom.FormallyEtale.comp ?_ (iso_stalk_formallyEtale _ _)
  exact RingHom.FormallyEtale.comp (iso_stalk_formallyEtale _ _)
    (Hs_stalk_formallyEtale k h2 _ hx hy)

include p in
theorem Hs_finite : IsFinite (Hs k) := by
  haveI : IsFinite (Hs k ≫ nu k p) := by
    rw [Hs_nu]
    infer_instance
  exact IsFinite.of_comp (Hs k) (nu k p)

theorem lift_finite : IsFinite (lift k p) := by
  haveI := Hs_finite k p
  unfold lift
  infer_instance


theorem lift_dominant : IsDominant (lift k p) := by
  haveI : Surjective (lift k p) := by
    haveI : Surjective (Hs k) := by
      haveI := Hs_finite k p
      have hfin : (square k).toRingHom.Finite :=
        (IsFinite.SpecMap_iff (CommRingCat.ofHom (square k).toRingHom)).mp (Hs_finite k p)
      rw [surjective_iff]
      exact hfin.to_isIntegral.comap_surjective (square_injective k)
    unfold lift
    infer_instance
  infer_instance

include p in
theorem Hs_surjective : Surjective (Hs k) := by
  have hfin : (square k).toRingHom.Finite :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (square k).toRingHom)).mp (Hs_finite k p)
  rw [surjective_iff]
  exact hfin.to_isIntegral.comap_surjective (square_injective k)

/-- The axes are codimension one. -/
theorem axisPt_coheight (i : Fin 2) : Order.coheight (axisPt k i) = 1 := by
  rw [← AlgebraicGeometry.idealHeight_eq_coheight]
  let P : Ideal (Plane k) := Ideal.span {(X i : Plane k)}
  haveI : P.IsPrime := (axisPt k i).2
  change P.height = 1
  apply le_antisymm
  · apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · have hbot : (⊥ : Ideal (Plane k)) < P := by
      rw [bot_lt_iff_ne_bot]
      intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact X_ne_zero i h
    have h0 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    rwa [Ideal.height_bot, zero_add] at h0

include p in
/-- `H` fixes the generic points of the two axes. -/
theorem Hs_axisPt (i : Fin 2) : Hs k (axisPt k i) = axisPt k i := by
  haveI := Hs_finite k p
  haveI := Hs_surjective k p
  haveI : Pcf.IsNormalScheme (Spec (.of (Plane k))) :=
    Pcf.Examples.PaperP.FrobeniusLine.plane_isNormalScheme k
  have hcoh0 := axisPt_coheight k i
  let A : Pcf.SchemeDivisorPoint (Spec (.of (Plane k))) := ⟨axisPt k i, hcoh0⟩
  apply eq_axisPt k _ (Pcf.coheight_apply_eq_one (Hs k) A) i
  change (X i : Plane k) ∈ (Ideal.span {(X i : Plane k)}).comap (square k).toRingHom
  rw [Ideal.mem_comap]
  change square k (X i) ∈ _
  rw [Ideal.mem_span_singleton]
  fin_cases i
  · exact ⟨X 0, by simp [square, x, pow_two]⟩
  · exact ⟨X 1, by simp [square, y, pow_two]⟩


/-! ### Weighted branch divisors lie over the axes -/

/-- A normalized divisor of weighted degree `> 1` for the lift is one of the two axes. -/
theorem delta_gt_one_axis (h2 : (2 : k) ≠ 0)
    (d : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Xs k p)))
    (hd : 1 < Pcf.schemeDivisorDelta (lift k p) d) :
    ∃ i : Fin 2, (normIso k p).hom d.1 = axisPt k i := by
  haveI := lift_finite k p
  have hcoh : Order.coheight ((normIso k p).hom d.1) = 1 :=
    (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (normIso k p).hom).trans d.2
  by_cases h0 : (X 0 : Plane k) ∈ ((normIso k p).hom d.1).asIdeal
  · exact ⟨0, eq_axisPt k _ hcoh 0 h0⟩
  by_cases h1 : (X 1 : Plane k) ∈ ((normIso k p).hom d.1).asIdeal
  · exact ⟨1, eq_axisPt k _ hcoh 1 h1⟩
  exfalso
  have := Pcf.schemeDivisorDelta_eq_one_of_formallyEtale (lift k p) d
    (lift_stalk_formallyEtale k p h2 d.1 h0 h1)
  omega

/-- The points of `X` under the two axes. -/
noncomputable def axisImage (i : Fin 2) : Xs k p := nu k p (axisPt k i)

theorem f_axisImage (i : Fin 2) :
    descendedSchemeMap k p (axisImage k p i) = axisImage k p i := by
  unfold axisImage
  rw [← Scheme.Hom.comp_apply, ← Hs_nu, Scheme.Hom.comp_apply, Hs_axisPt k p i]

instance normalizationFinite : IsFinite (Pcf.Palomar.normalizationMap (Xs k p)) :=
  BirationalAffineNormalization.normalizationMap_isFinite (ring k p) (Plane k)

/-- **The normalized weighted branch locus of `f` lies over the two axes.** -/
theorem weightedBranchPointSet_subset (h2 : (2 : k) ≠ 0) :
    Pcf.weightedBranchPointSet (descendedSchemeMap k p) ⊆
      Set.range (axisImage k p) := by
  rintro q ⟨r, ⟨d, hdr, hd⟩, rfl⟩
  have hF := (lift_eq_canonical k p).symm
  rw [hF] at hd
  obtain ⟨i, hi⟩ := delta_gt_one_axis k p h2 d hd
  refine ⟨i, ?_⟩
  subst hdr
  change axisImage k p i = Pcf.Palomar.normalizationMap (Xs k p)
    (Pcf.schemeGlobalNormalizationMorphism (descendedSchemeMap k p) d.1)
  rw [hF, ← Scheme.Hom.comp_apply, lift_comp_normalizationMap, Scheme.Hom.comp_apply,
    ← normIso_hom_nu, Scheme.Hom.comp_apply, hi]
  exact (f_axisImage k p i).symm


theorem weightedPostcriticalPointSet_subset (h2 : (2 : k) ≠ 0) :
    Pcf.weightedPostcriticalPointSet (descendedSchemeMap k p) ⊆ Set.range (axisImage k p) := by
  intro q hq
  simp only [Pcf.weightedPostcriticalPointSet, Set.mem_iUnion] at hq
  obtain ⟨n, z, hz, rfl⟩ := hq
  obtain ⟨i, rfl⟩ := weightedBranchPointSet_subset k p h2 hz
  refine ⟨i, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      change axisImage k p i = (descendedSchemeMap k p : _ → _)^[n + 1] (axisImage k p i)
      rw [Function.iterate_succ_apply']
      rw [← show axisImage k p i = (descendedSchemeMap k p : _ → _)^[n] (axisImage k p i)
        from ih, f_axisImage]

/-- The structure morphism `X → Spec k`. -/
noncomputable def structureMap : Xs k p ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (ring k p)))

instance structureMap_finiteType : LocallyOfFiniteType (structureMap k p) := by
  haveI := ring_finiteType k p
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- `f` is generically separable. -/
theorem f_isGenericallySeparable (h2 : (2 : k) ≠ 0) :
    Pcf.IsGenericallySeparable (descendedSchemeMap k p) := by
  haveI := Hs_finite k p
  haveI := Hs_surjective k p
  have hgen : ((Hs k).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.FormallyEtale := by
    apply Hs_stalk_formallyEtale k h2
    · rw [genericPoint_eq_bot_of_affine]; exact X_ne_zero 0
    · rw [genericPoint_eq_bot_of_affine]; exact X_ne_zero 1
  exact Pcf.isGenericallySeparable_of_finite_commuting_square (descendedSchemeMap k p) (Hs k)
    (nu k p) (Hs_nu k p) (Pcf.isGenericallySeparableSchemeMap_of_formallyEtale_generic _ hgen)

/-- **`ex:frobenius-pinching`: `f` is PCF.** If `2 ≠ 0` in `k`, the descended map `f` on the
pinched surface satisfies the paper's separable normalized PCF predicate: it is generically
separable and its weighted postcritical set (computed on the normalization `A²`) is finite,
contained in the images of the two axes. -/
theorem f_isSeparableNormalizedPCF (h2 : (2 : k) ≠ 0) :
    Pcf.IsSeparableNormalizedPCF k (structureMap k p) (descendedSchemeMap k p) := by
  apply (Pcf.isSeparableNormalizedPCF_iff_downstairs k (structureMap k p) _).2
  refine ⟨f_isGenericallySeparable k p h2, ?_⟩
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k
    (structureMap k p) _).2
  exact (Set.finite_range _).subset (weightedPostcriticalPointSet_subset k p h2)

/-- `2 ≠ 0` in characteristic `p ≥ 3`. -/
theorem two_ne_zero_of_charP [CharP k p] (hp : 3 ≤ p) : (2 : k) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k p] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

/-- The manuscript's hypotheses: `char k = p ≥ 5`.

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem f_isSeparableNormalizedPCF_of_charP [CharP k p] (hp : 5 ≤ p) :
    Pcf.IsSeparableNormalizedPCF k (structureMap k p) (descendedSchemeMap k p) :=
  f_isSeparableNormalizedPCF k p (two_ne_zero_of_charP k p (by omega))

#print axioms lift_stalk_formallyEtale
#print axioms Hs_axisPt
#print axioms delta_gt_one_axis
#print axioms weightedBranchPointSet_subset
#print axioms f_isGenericallySeparable
#print axioms f_isSeparableNormalizedPCF
#print axioms f_isSeparableNormalizedPCF_of_charP

end Pcf.Examples.PaperP.FrobeniusPinchingPCF
