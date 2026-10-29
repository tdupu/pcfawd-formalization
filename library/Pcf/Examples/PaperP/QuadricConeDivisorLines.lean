/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeRestriction
public import Pcf.Examples.PaperP.QuadricConeNormal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The two actual closed affine lines in the cone example

The quotients defining `A=V(v)` and `B=V(y,z)` are polynomial rings in one
variable. The ambient coordinate map gives the squaring map on these lines.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConeDivisorLines

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

@[local simp] private theorem liftAlgQuotient_mk {K R S : Type*}
    [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (I : Ideal R) (f : R →ₐ[K] S) (h : ∀ r ∈ I, f r = 0) (r : R) :
    Ideal.Quotient.liftₐ I f h (Ideal.Quotient.mk I r) = f r := rfl

variable (k : Type*) [Field k]

noncomputable def sourceIdeal : Ideal (QuadricConeAmbientFinite.Plane k) :=
  Ideal.span {QuadricConeAmbientFinite.v k}

noncomputable def targetIdeal : Ideal (QuadricConeInjective.CoordinateRing k) :=
  Ideal.span {QuadricConeInjective.y k, QuadricConeInjective.z k}

noncomputable def sourceEvaluation : QuadricConeAmbientFinite.Plane k →ₐ[k] (Polynomial k) :=
  MvPolynomial.aeval ![Polynomial.X, 0]

noncomputable def targetEvaluation :
    QuadricConeInjective.CoordinateRing k →ₐ[k] (Polynomial k) :=
  Ideal.Quotient.liftₐ (Cusp.coneIdeal k) (MvPolynomial.aeval ![Polynomial.X, 0, 0]) (by
    intro p hp
    have hle : Cusp.coneIdeal k ≤ RingHom.ker
        (MvPolynomial.aeval ![(Polynomial.X : (Polynomial k)), 0, 0]).toRingHom := by
      rw [Cusp.coneIdeal, Ideal.span_singleton_le_iff_mem]
      simp [RingHom.mem_ker]
    exact hle hp)

@[simp] theorem sourceEvaluation_u :
    sourceEvaluation k (QuadricConeAmbientFinite.u k) = Polynomial.X := by
  simp [sourceEvaluation, QuadricConeAmbientFinite.u]

@[simp] theorem sourceEvaluation_v :
    sourceEvaluation k (QuadricConeAmbientFinite.v k) = 0 := by
  simp [sourceEvaluation, QuadricConeAmbientFinite.v]

@[simp] theorem targetEvaluation_x :
    targetEvaluation k (QuadricConeInjective.x k) = Polynomial.X := by
  simp [targetEvaluation, QuadricConeInjective.x]

@[simp] theorem targetEvaluation_y :
    targetEvaluation k (QuadricConeInjective.y k) = 0 := by
  simp [targetEvaluation, QuadricConeInjective.y]

@[simp] theorem targetEvaluation_z :
    targetEvaluation k (QuadricConeInjective.z k) = 0 := by
  simp [targetEvaluation, QuadricConeInjective.z]

noncomputable def sourceQuotientMap :
    (QuadricConeAmbientFinite.Plane k ⧸ sourceIdeal k) →ₐ[k] (Polynomial k) :=
  Ideal.Quotient.liftₐ _ (sourceEvaluation k) (by
    intro p hp
    have hle : sourceIdeal k ≤ RingHom.ker (sourceEvaluation k).toRingHom := by
      rw [sourceIdeal, Ideal.span_singleton_le_iff_mem]
      exact sourceEvaluation_v k
    exact hle hp)

noncomputable def targetQuotientMap :
    (QuadricConeInjective.CoordinateRing k ⧸ targetIdeal k) →ₐ[k] (Polynomial k) :=
  Ideal.Quotient.liftₐ _ (targetEvaluation k) (by
    intro p hp
    have hle : targetIdeal k ≤ RingHom.ker (targetEvaluation k).toRingHom := by
      rw [targetIdeal, Ideal.span_le]
      rintro q (rfl | rfl)
      · exact targetEvaluation_y k
      · exact targetEvaluation_z k
    exact hle hp)

noncomputable def sourceQuotientInverse :
    (Polynomial k) →ₐ[k] (QuadricConeAmbientFinite.Plane k ⧸ sourceIdeal k) :=
  Polynomial.aeval (Ideal.Quotient.mk _ (QuadricConeAmbientFinite.u k))

noncomputable def targetQuotientInverse :
    (Polynomial k) →ₐ[k] (QuadricConeInjective.CoordinateRing k ⧸ targetIdeal k) :=
  Polynomial.aeval (Ideal.Quotient.mk _ (QuadricConeInjective.x k))

noncomputable def sourceQuotientEquiv :
    (QuadricConeAmbientFinite.Plane k ⧸ sourceIdeal k) ≃ₐ[k] (Polynomial k) := by
  apply AlgEquiv.ofAlgHom (sourceQuotientMap k) (sourceQuotientInverse k)
  · apply Polynomial.algHom_ext
    simp [sourceQuotientMap, sourceQuotientInverse]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [sourceQuotientMap, sourceQuotientInverse, sourceEvaluation,
        QuadricConeAmbientFinite.u]
    · have hv : Ideal.Quotient.mk (sourceIdeal k) (QuadricConeAmbientFinite.v k) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      simpa [sourceQuotientMap, sourceQuotientInverse, sourceEvaluation,
        QuadricConeAmbientFinite.v] using hv.symm

noncomputable def targetQuotientEquiv :
    (QuadricConeInjective.CoordinateRing k ⧸ targetIdeal k) ≃ₐ[k] (Polynomial k) := by
  apply AlgEquiv.ofAlgHom (targetQuotientMap k) (targetQuotientInverse k)
  · apply Polynomial.algHom_ext
    simp [targetQuotientMap, targetQuotientInverse]
  · apply Ideal.Quotient.algHom_ext
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [targetQuotientMap, targetQuotientInverse, targetEvaluation,
        QuadricConeInjective.x]
    · have hy : Ideal.Quotient.mk (targetIdeal k) (QuadricConeInjective.y k) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl rfl))
      simpa [targetQuotientMap, targetQuotientInverse, targetEvaluation,
        QuadricConeInjective.y] using hy.symm
    · have hz : Ideal.Quotient.mk (targetIdeal k) (QuadricConeInjective.z k) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr rfl))
      simpa [targetQuotientMap, targetQuotientInverse, targetEvaluation,
        QuadricConeInjective.z] using hz.symm

/-- The actual scheme `V(v)` is an affine line. -/
noncomputable def sourceSchemeIso :
    Spec (.of (QuadricConeAmbientFinite.Plane k ⧸ sourceIdeal k)) ≅ Spec (.of (Polynomial k)) :=
  (Scheme.Spec.mapIso (sourceQuotientEquiv k).toRingEquiv.toCommRingCatIso.op).symm

/-- The actual scheme `V(y,z)` on the cone is an affine line. -/
noncomputable def targetSchemeIso :
    Spec (.of (QuadricConeInjective.CoordinateRing k ⧸ targetIdeal k)) ≅ Spec (.of (Polynomial k)) :=
  (Scheme.Spec.mapIso (targetQuotientEquiv k).toRingEquiv.toCommRingCatIso.op).symm

/-- Squaring is the restriction of the actual cone parametrization to these two lines. -/
theorem restriction_coordinate_square :
    (sourceEvaluation k).comp (QuadricConeAmbientFinite.map k) =
      (QuadricConeRestriction.coordinateMap k).comp (targetEvaluation k) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [sourceEvaluation, targetEvaluation, QuadricConeAmbientFinite.map,
      Cusp.coneParam, Cusp.coneMap, QuadricConeRestriction.coordinateMap_X]

/-- The kernel of the source-line evaluation is exactly `(v)`. -/
theorem sourceEvaluation_ker :
    RingHom.ker (sourceEvaluation k).toRingHom = sourceIdeal k := by
  ext p
  change sourceEvaluation k p = 0 ↔ p ∈ sourceIdeal k
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hp => (sourceQuotientEquiv k).injective (by
    change sourceEvaluation k p = sourceQuotientEquiv k 0
    simpa using hp), fun hp => by
      have := congrArg (sourceQuotientEquiv k) hp
      simpa [sourceQuotientEquiv, sourceQuotientMap] using this⟩

/-- The kernel of the target-line evaluation is exactly `(y,z)`. -/
theorem targetEvaluation_ker :
    RingHom.ker (targetEvaluation k).toRingHom = targetIdeal k := by
  ext p
  change targetEvaluation k p = 0 ↔ p ∈ targetIdeal k
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hp => (targetQuotientEquiv k).injective (by
    change targetEvaluation k p = targetQuotientEquiv k 0
    simpa using hp), fun hp => by
      have := congrArg (targetQuotientEquiv k) hp
      simpa [targetQuotientEquiv, targetQuotientMap] using this⟩

theorem sourceEvaluation_surjective : Function.Surjective (sourceEvaluation k) := by
  intro p
  obtain ⟨q, hq⟩ := (sourceQuotientEquiv k).surjective p
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨r, hq⟩

theorem targetEvaluation_surjective : Function.Surjective (targetEvaluation k) := by
  intro p
  obtain ⟨q, hq⟩ := (targetQuotientEquiv k).surjective p
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨r, hq⟩

/-- The source affine line embedded as the actual closed subscheme `V(v)`. -/
noncomputable def sourceEmbedding :
    Spec (.of (Polynomial k)) ⟶ Spec (.of (QuadricConeAmbientFinite.Plane k)) :=
  Spec.map (CommRingCat.ofHom (sourceEvaluation k).toRingHom)

/-- The target affine line embedded as the actual closed subscheme `V(y,z)`. -/
noncomputable def targetEmbedding :
    Spec (.of (Polynomial k)) ⟶ Spec (.of (QuadricConeInjective.CoordinateRing k)) :=
  Spec.map (CommRingCat.ofHom (targetEvaluation k).toRingHom)

theorem sourceEmbedding_isClosedImmersion : IsClosedImmersion (sourceEmbedding k) :=
  IsClosedImmersion.spec_of_surjective _ (sourceEvaluation_surjective k)

theorem targetEmbedding_isClosedImmersion : IsClosedImmersion (targetEmbedding k) :=
  IsClosedImmersion.spec_of_surjective _ (targetEvaluation_surjective k)

/-- The underlying image of the source embedding is exactly `V(v)`. -/
theorem sourceEmbedding_range : Set.range (sourceEmbedding k) =
    PrimeSpectrum.zeroLocus (sourceIdeal k) := by
  change Set.range (PrimeSpectrum.comap (sourceEvaluation k).toRingHom) = _
  rw [range_comap_of_surjective _ _ (sourceEvaluation_surjective k),
    sourceEvaluation_ker]

/-- The underlying image of the target embedding is exactly `V(y,z)`. -/
theorem targetEmbedding_range : Set.range (targetEmbedding k) =
    PrimeSpectrum.zeroLocus (targetIdeal k) := by
  change Set.range (PrimeSpectrum.comap (targetEvaluation k).toRingHom) = _
  rw [range_comap_of_surjective _ _ (targetEvaluation_surjective k),
    targetEvaluation_ker]

/-- The actual affine-line morphism is the restriction of the ambient morphism
along these two closed immersions. -/
theorem restriction_scheme_square :
    sourceEmbedding k ≫ QuadricConeAmbientFinite.schemeMap k =
      QuadricConeRestriction.schemeMap k ≫ targetEmbedding k := by
  unfold sourceEmbedding targetEmbedding QuadricConeAmbientFinite.schemeMap
    QuadricConeRestriction.schemeMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h : QuadricConeInjective.CoordinateRing k →ₐ[k] Polynomial k =>
    Spec.map (CommRingCat.ofHom h.toRingHom)) (restriction_coordinate_square k)

/-- The ambient parametrization maps `A=V(v)` onto `B=V(y,z)`. -/
theorem ambient_image_sourceLine :
    QuadricConeAmbientFinite.schemeMap k '' PrimeSpectrum.zeroLocus (sourceIdeal k) =
      PrimeSpectrum.zeroLocus (targetIdeal k) := by
  rw [← sourceEmbedding_range, ← targetEmbedding_range, ← Set.range_comp]
  have hfunc : (QuadricConeAmbientFinite.schemeMap k) ∘ sourceEmbedding k =
      targetEmbedding k ∘ QuadricConeRestriction.schemeMap k :=
    congrArg (fun h => (fun p => h p)) (restriction_scheme_square k)
  rw [hfunc, Set.range_comp]
  have hsurj := (surjective_iff (QuadricConeRestriction.schemeMap k)).mp
    (QuadricConeRestriction.schemeMap_surjective k)
  rw [hsurj.range_eq, Set.image_univ]

/-- The source line is integral and has codimension one. -/
theorem sourceIdeal_isPrime_height_one :
    (sourceIdeal k).IsPrime ∧ (sourceIdeal k).height = 1 := by
  have hv : Prime (QuadricConeAmbientFinite.v k) :=
    MvPolynomial.X_prime (R := k) (i := (1 : Fin 2))
  constructor
  · exact (Ideal.span_singleton_prime hv.ne_zero).mpr hv
  · exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hv.ne_zero) hv.not_isUnit

/-- The defining ideal of the target line contracts from the source line. -/
theorem targetIdeal_eq_comap_sourceIdeal :
    targetIdeal k = (sourceIdeal k).comap (QuadricConeAmbientFinite.map k).toRingHom := by
  rw [← targetEvaluation_ker, ← sourceEvaluation_ker]
  ext p
  change targetEvaluation k p = 0 ↔
    sourceEvaluation k (QuadricConeAmbientFinite.map k p) = 0
  have h := congrArg (fun h => h p) (restriction_coordinate_square k)
  change sourceEvaluation k (QuadricConeAmbientFinite.map k p) =
    QuadricConeRestriction.coordinateMap k (targetEvaluation k p) at h
  rw [h]
  exact ⟨fun hp => by rw [hp, map_zero], fun hp =>
    (QuadricConeRestriction.coordinateMap_injective k) (by simpa only [map_zero] using hp)⟩

/-- The target line is also an integral effective divisor on the actual cone. -/
theorem targetIdeal_isPrime_height_one [CharZero k] :
    (targetIdeal k).IsPrime ∧ (targetIdeal k).height = 1 := by
  haveI : (sourceIdeal k).IsPrime := (sourceIdeal_isPrime_height_one k).1
  haveI : Module.Finite (QuadricConeInjective.CoordinateRing k)
      (QuadricConeAmbientFinite.Plane k) := QuadricConeAmbientFinite.moduleFinite k
  rw [targetIdeal_eq_comap_sourceIdeal]
  constructor
  · infer_instance
  · exact (Pcf.height_under_eq_of_finite_of_finiteType k (sourceIdeal k)).trans
      (sourceIdeal_isPrime_height_one k).2

#print axioms sourceQuotientEquiv
#print axioms targetQuotientEquiv
#print axioms sourceSchemeIso
#print axioms targetSchemeIso
#print axioms restriction_coordinate_square
#print axioms sourceEvaluation_ker
#print axioms targetEvaluation_ker
#print axioms sourceEmbedding_isClosedImmersion
#print axioms targetEmbedding_isClosedImmersion
#print axioms restriction_scheme_square
#print axioms sourceEmbedding_range
#print axioms targetEmbedding_range
#print axioms ambient_image_sourceLine
#print axioms sourceIdeal_isPrime_height_one
#print axioms targetIdeal_eq_comap_sourceIdeal
#print axioms targetIdeal_isPrime_height_one

end Pcf.Examples.PaperP.QuadricConeDivisorLines
