/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CuspAbsoluteNormalization
public import Pcf.Bounding.TheoremAWeightedDownstairs
public import Pcf.Bounding.SchemePurelyInseparableDelta
/-!
# The canonical normalization lift of the cusp parametrization

For `latex/paper-p.tex`, Example `ex:cusp`, the explicit lift agrees with the
library's functorial normalization morphism. Its isomorphism property gives
empty normalized non-étale and weighted branch loci. The ambient plane branch
calculation is a separate obligation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
namespace Pcf.Examples.PaperP.CuspOriginalFibre
variable (k : Type*) [Field k] [CharZero k]
set_option linter.style.haveILetI false
omit [CharZero k] in
/-- Maps from the parameter ring to a domain are determined by their
restrictions to the cusp ring: the square and cube determine the parameter. -/
private theorem cuspParam_cancel_to_domain {R : Type*} [CommRing R] [IsDomain R]
    {a b : k[X] →+* R}
    (h : a.comp (Pcf.Examples.Cusp.cuspParam k).toRingHom =
      b.comp (Pcf.Examples.Cusp.cuspParam k).toRingHom) : a = b := by
  apply Polynomial.ringHom_ext
  · intro r
    have hr := DFunLike.congr_fun h (algebraMap k (CoordinateRing k) r)
    simpa using hr
  · have h2 : a X ^ 2 = b X ^ 2 := by
      have hx := DFunLike.congr_fun h
        (Ideal.Quotient.mk _ (MvPolynomial.X (0 : Fin 2)))
      simpa using hx
    have h3 : a X ^ 3 = b X ^ 3 := by
      have hy := DFunLike.congr_fun h
        (Ideal.Quotient.mk _ (MvPolynomial.X (1 : Fin 2)))
      simpa using hy
    by_cases ha : a X = 0
    · have hb : b X = 0 := (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
        (by rw [← h2, ha]; simp)
      rw [ha, hb]
    · apply mul_right_cancel₀ (pow_ne_zero 2 ha)
      calc
        a X * a X ^ 2 = a X ^ 3 := by ring
        _ = b X ^ 3 := h3
        _ = b X * a X ^ 2 := by rw [h2]; ring

/-- The generic cusp parametrization recovers the parameter generic point. -/
theorem cuspGenericInclusion_comp :
    Pcf.schemeGenericInclusion (Spec (.of k[X])) =
      @Pcf.schemeGenericMorphism _ _ _ _ (schemeMap k) (cuspSchemeMap_isDominant k) ≫
        cuspGenericToParameterLine k := by
  letI : IsDominant (schemeMap k) := cuspSchemeMap_isDominant k
  let Y := Spec (.of k[X])
  let f := Pcf.schemeGenericInclusion Y
  let g := Pcf.schemeGenericMorphism (schemeMap k) ≫ cuspGenericToParameterLine k
  have h : f ≫ schemeMap k = g ≫ schemeMap k := by
    dsimp [f, g]
    rw [Category.assoc, cuspGenericToParameterLine_comp,
      Pcf.schemeGenericMorphism_comp]
  obtain ⟨a, ha⟩ := Spec.map_surjective (R := .of k[X]) (S := Y.functionField) f
  obtain ⟨b, hb⟩ := Spec.map_surjective (R := .of k[X]) (S := Y.functionField) g
  change f = g
  rw [← ha, ← hb] at h ⊢
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply cuspParam_cancel_to_domain k
  unfold schemeMap at h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
/-- The over-cusp comparison preserves the specified generic point. -/
theorem cuspNormalizationToParameterLine_generic :
    Pcf.Palomar.genericToNormalization (Spec (.of (CoordinateRing k))) ≫
      cuspNormalizationToParameterLine k = cuspGenericToParameterLine k := by
  letI : IsFinite (schemeMap k) := schemeMap_isFinite k
  exact (Pcf.schemeGenericInclusion (Spec (.of (CoordinateRing k)))).toNormalization_normalizationDesc
    (cuspGenericToParameterLine k) (schemeMap k) (cuspGenericToParameterLine_comp k).symm

/-- The explicit normalized lift is the library's canonical lift. -/
theorem cuspNormalizedLift_eq_canonical :
    letI : IsFinite (schemeMap k) := schemeMap_isFinite k
    letI : IsDominant (schemeMap k) := cuspSchemeMap_isDominant k
    cuspNormalizedLift k = Pcf.schemeGlobalNormalizationMorphism (schemeMap k) := by
  letI : IsFinite (schemeMap k) := schemeMap_isFinite k
  letI : IsDominant (schemeMap k) := cuspSchemeMap_isDominant k
  letI : IsIso (cuspNormalizationToParameterLine k) := cuspNormalizationToParameterLine_isIso k
  apply Pcf.schemeGlobalNormalizationMorphism_unique
  · exact cuspNormalizedLift_comp k
  · apply (cancel_mono (cuspNormalizationToParameterLine k)).mp
    simp only [Category.assoc]
    rw [cuspNormalizationToParameterLine_generic]
    unfold cuspNormalizedLift
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [Pcf.schemeGenericToNormalization_comp]
    exact cuspGenericInclusion_comp k
attribute [local instance] schemeMap_isFinite cuspSchemeMap_isDominant
  cuspParameterNormalizationMap_isIso

local instance cuspNormalizationFinite :
    IsFinite (Pcf.Palomar.normalizationMap (Spec (.of (CoordinateRing k)))) := by
  rw [← cuspNormalizationToParameterLine_comp k]
  letI : IsIso (cuspNormalizationToParameterLine k) := cuspNormalizationToParameterLine_isIso k
  infer_instance

/-- The canonical lift to absolute normalizations is an isomorphism. -/
theorem cuspCanonicalLift_isIso :
    IsIso (Pcf.schemeGlobalNormalizationMorphism (schemeMap k)) := by
  rw [← cuspNormalizedLift_eq_canonical k]
  exact cuspNormalizedLift_isIso k

/-- The canonical lift is étale at every point. -/
theorem cuspCanonicalLift_nonEtaleLocus_empty :
    {x : Pcf.Palomar.normalization (Spec (.of k[X])) |
      ¬ Pcf.Stacks.IsStacksEtaleAt
        (Pcf.schemeGlobalNormalizationMorphism (schemeMap k)) x} = ∅ := by
  rw [← cuspNormalizedLift_eq_canonical k]
  exact cuspNormalizedLift_nonEtaleLocus_empty k

/-- No divisor of the parameter normalization has weighted degree above one. -/
theorem cusp_weightedCriticalPointSet_empty :
    Pcf.weightedCriticalPointSet (schemeMap k) = ∅ := by
  letI : IsIso (Pcf.schemeGlobalNormalizationMorphism (schemeMap k)) :=
    cuspCanonicalLift_isIso k
  simp [Pcf.weightedCriticalPointSet, Pcf.schemeDivisorDelta_of_isIso]

/-- The manuscript's normalized weighted branch locus of the cusp map is empty. -/
theorem cusp_weightedBranchLocus_empty :
    Pcf.weightedBranchLocus (schemeMap k) = ∅ := by
  rw [Pcf.weightedBranchLocus_eq_image_criticalLocus]
  simp [Pcf.weightedCriticalLocus, cusp_weightedCriticalPointSet_empty]
#print axioms cuspGenericInclusion_comp
#print axioms cuspNormalizationToParameterLine_generic
#print axioms cuspNormalizedLift_eq_canonical
#print axioms cuspCanonicalLift_isIso
#print axioms cuspCanonicalLift_nonEtaleLocus_empty
#print axioms cusp_weightedCriticalPointSet_empty
#print axioms cusp_weightedBranchLocus_empty

end Pcf.Examples.PaperP.CuspOriginalFibre
