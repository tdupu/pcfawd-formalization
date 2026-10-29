/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineMap
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The actual invariant line and its Frobenius restriction

The quotient by `v` is an affine line. The ambient map restricts to the
`k`-linear power map `u ↦ u^p`, represented by `Polynomial.expand k p`.
The defining divisor ideal pulls back unchanged, and its ring ramification
index is one, including in characteristic `p`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

@[local simp] private theorem liftAlgQuotient_mk {K R S : Type*}
    [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (I : Ideal R) (f : R →ₐ[K] S) (h : ∀ r ∈ I, f r = 0) (r : R) :
    Ideal.Quotient.liftₐ I f h (Ideal.Quotient.mk I r) = f r := rfl

variable (k : Type*) [Field k] (p : ℕ)

noncomputable def lineIdeal : Ideal (Plane k) := Ideal.span {v k}

noncomputable def lineEvaluation : Plane k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval ![Polynomial.X, 0]

@[simp] theorem lineEvaluation_u : lineEvaluation k (u k) = Polynomial.X := by
  simp [lineEvaluation, u]

@[simp] theorem lineEvaluation_v : lineEvaluation k (v k) = 0 := by
  simp [lineEvaluation, v]

noncomputable def lineQuotientMap : (Plane k ⧸ lineIdeal k) →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ _ (lineEvaluation k) (by
    intro q hq
    have hle : lineIdeal k ≤ RingHom.ker (lineEvaluation k).toRingHom := by
      rw [lineIdeal, Ideal.span_singleton_le_iff_mem]
      exact lineEvaluation_v k
    exact hle hq)

noncomputable def lineQuotientInverse : Polynomial k →ₐ[k] (Plane k ⧸ lineIdeal k) :=
  Polynomial.aeval (Ideal.Quotient.mk _ (u k))

noncomputable def lineQuotientEquiv : (Plane k ⧸ lineIdeal k) ≃ₐ[k] Polynomial k := by
  apply AlgEquiv.ofAlgHom (lineQuotientMap k) (lineQuotientInverse k)
  · apply Polynomial.algHom_ext
    simp [lineQuotientMap, lineQuotientInverse]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [lineQuotientMap, lineQuotientInverse, lineEvaluation, u]
    · have hv : Ideal.Quotient.mk (lineIdeal k) (v k) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      simpa [lineQuotientMap, lineQuotientInverse, lineEvaluation, v] using hv.symm

theorem lineEvaluation_surjective : Function.Surjective (lineEvaluation k) := by
  intro q
  obtain ⟨r, hr⟩ := (lineQuotientEquiv k).surjective q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨s, hr⟩

theorem lineEvaluation_ker : RingHom.ker (lineEvaluation k).toRingHom = lineIdeal k := by
  ext q
  change lineEvaluation k q = 0 ↔ q ∈ lineIdeal k
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hq => (lineQuotientEquiv k).injective (by
    change lineEvaluation k q = lineQuotientEquiv k 0
    simpa using hq), fun hq => by
      have := congrArg (lineQuotientEquiv k) hq
      simpa [lineQuotientEquiv, lineQuotientMap] using this⟩

/-- The relative power map fixes coefficients in `k`; this is the manuscript's
Frobenius restriction, distinguished from absolute Frobenius on coefficients. -/
noncomputable def lineCoordinateMap : Polynomial k →ₐ[k] Polynomial k := Polynomial.expand k p

@[simp] theorem lineCoordinateMap_X : lineCoordinateMap k p Polynomial.X = Polynomial.X ^ p :=
  Polynomial.expand_X p

theorem lineCoordinateMap_injective (hp : 0 < p) : Function.Injective (lineCoordinateMap k p) :=
  Polynomial.expand_injective hp

/-- This is an equality of maps on the actual ambient coordinate ring. -/
theorem restriction_coordinate_square :
    (lineEvaluation k).comp (coordinateMap k p) =
      (lineCoordinateMap k p).comp (lineEvaluation k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [lineEvaluation, coordinateMap, u, v, lineCoordinateMap_X]

/-- The relative Frobenius restriction is finite. -/
theorem lineCoordinateMap_finite (hp : 2 ≤ p) : (lineCoordinateMap k p).toRingHom.Finite := by
  apply RingHom.Finite.of_comp_finite (f := (lineEvaluation k).toRingHom)
  have h := congrArg AlgHom.toRingHom (restriction_coordinate_square k p)
  change (lineEvaluation k).toRingHom.comp (coordinateMap k p).toRingHom =
    (lineCoordinateMap k p).toRingHom.comp (lineEvaluation k).toRingHom at h
  rw [← h]
  exact (RingHom.Finite.of_surjective _ (lineEvaluation_surjective k)).comp
    (coordinateMap_finite k p hp)

noncomputable def lineSchemeMap : Spec (.of (Polynomial k)) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (lineCoordinateMap k p).toRingHom)

noncomputable def lineEmbedding : Spec (.of (Polynomial k)) ⟶ Spec (.of (Plane k)) :=
  Spec.map (CommRingCat.ofHom (lineEvaluation k).toRingHom)

/-- `paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineSchemeMap_finite (hp : 2 ≤ p) : IsFinite (lineSchemeMap k p) :=
  (IsFinite.SpecMap_iff _).mpr (lineCoordinateMap_finite k p hp)

/-- `paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineSchemeMap_surjective (hp : 2 ≤ p) : Surjective (lineSchemeMap k p) := by
  rw [surjective_iff]
  exact (lineCoordinateMap_finite k p hp).to_isIntegral.comap_surjective
    (lineCoordinateMap_injective k p (by omega))

theorem lineEmbedding_isClosedImmersion : IsClosedImmersion (lineEmbedding k) :=
  IsClosedImmersion.spec_of_surjective _ (lineEvaluation_surjective k)

theorem lineEmbedding_range :
    Set.range (lineEmbedding k) = PrimeSpectrum.zeroLocus (lineIdeal k) := by
  change Set.range (PrimeSpectrum.comap (lineEvaluation k).toRingHom) = _
  rw [range_comap_of_surjective _ _ (lineEvaluation_surjective k), lineEvaluation_ker]

/-- The restriction square uses actual scheme maps and a closed affine-line embedding.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem restriction_scheme_square : lineEmbedding k ≫ schemeMap k p =
    lineSchemeMap k p ≫ lineEmbedding k := by
  unfold lineEmbedding schemeMap lineSchemeMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h : Plane k →ₐ[k] Polynomial k =>
    Spec.map (CommRingCat.ofHom h.toRingHom)) (restriction_coordinate_square k p)

/-- The line `V(v)` is invariant as an underlying closed set. -/
theorem invariant_line_image (hp : 2 ≤ p) :
    schemeMap k p '' PrimeSpectrum.zeroLocus (lineIdeal k) =
      PrimeSpectrum.zeroLocus (lineIdeal k) := by
  rw [← lineEmbedding_range, ← Set.range_comp]
  have hfunc : (schemeMap k p) ∘ lineEmbedding k = lineEmbedding k ∘ lineSchemeMap k p :=
    congrArg (fun h => (fun q => h q)) (restriction_scheme_square k p)
  rw [hfunc, Set.range_comp]
  have hsurj := (surjective_iff (lineSchemeMap k p)).mp (lineSchemeMap_surjective k p hp)
  rw [hsurj.range_eq, Set.image_univ]

theorem lineIdeal_map : (lineIdeal k).map (coordinateMap k p).toRingHom = lineIdeal k := by
  rw [lineIdeal, Ideal.map_span]
  simp only [Set.image_singleton]
  change Ideal.span {coordinateMap k p (v k)} = Ideal.span {v k}
  rw [coordinateMap_v]

theorem lineIdeal_comap (hp : 0 < p) :
    (lineIdeal k).comap (coordinateMap k p).toRingHom = lineIdeal k := by
  rw [← lineEvaluation_ker]
  ext q
  change lineEvaluation k (coordinateMap k p q) = 0 ↔ lineEvaluation k q = 0
  have h := congrArg (fun h => h q) (restriction_coordinate_square k p)
  change lineEvaluation k (coordinateMap k p q) = lineCoordinateMap k p (lineEvaluation k q) at h
  rw [h]
  exact ⟨fun hq => (lineCoordinateMap_injective k p hp) (by simpa using hq),
    fun hq => by rw [hq, map_zero]⟩

private theorem ramificationIdx_eq_one_of_map_under {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime]
    (h : (q.under R).map (algebraMap R S) = q) : q.ramificationIdx R = 1 := by
  rw [Ideal.ramificationIdx_def, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q),
    ← Ideal.map_map, h, Localization.AtPrime.map_eq_maximalIdeal,
    ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact IsLocalRing.maximalIdeal.isMaximal _

/-- The ring ramification index along the actual invariant line is one.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineIdeal_ramificationIdx_eq_one (hp : 0 < p) :
    letI : Algebra (Plane k) (Plane k) := (coordinateMap k p).toRingHom.toAlgebra
    (lineIdeal k).ramificationIdx (Plane k) = 1 := by
  letI : Algebra (Plane k) (Plane k) := (coordinateMap k p).toRingHom.toAlgebra
  haveI : (lineIdeal k).IsPrime := by
    rw [← lineEvaluation_ker]
    exact RingHom.ker_isPrime _
  apply ramificationIdx_eq_one_of_map_under
  change ((lineIdeal k).comap (coordinateMap k p).toRingHom).map
    (coordinateMap k p).toRingHom = lineIdeal k
  rw [lineIdeal_comap k p hp, lineIdeal_map]

#print axioms lineQuotientEquiv
#print axioms lineCoordinateMap_finite
#print axioms restriction_scheme_square
#print axioms invariant_line_image
#print axioms lineIdeal_map
#print axioms lineIdeal_ramificationIdx_eq_one

end Pcf.Examples.PaperP.FrobeniusLine
