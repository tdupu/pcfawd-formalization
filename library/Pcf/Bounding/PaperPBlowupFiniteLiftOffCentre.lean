/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupFiniteLiftFamily
public import Pcf.Bounding.AllCodimBlowupIsoOffCentre
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite fibers of the normalized Rees map off the centre

The stalk isomorphism off the blow-up centre implies quasi-finiteness there.
Compactness of each scheme-theoretic fiber then makes its off-centre points
finite. This supplies the finite-lift premise for a fixed branch family.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

theorem finite_preimage_singleton_of_quasiFiniteAt_on_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y)
    (h : ∀ x, f x = y → f.QuasiFiniteAt x) :
    (f ⁻¹' {y}).Finite := by
  haveI : DiscreteTopology (f.fiber y) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    have hx : f.QuasiFiniteAt (f.fiberι y x) :=
      h _ (f.fiberHomeo y x).2
    have ho := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx
    have hy : f (f.fiberι y x) = y := (f.fiberHomeo y x).2
    generalize hu : f.fiberι y x = u at hx ho hy
    cases hy
    have hxu : x = f.asFiber u :=
      (f.fiberι (f u)).isEmbedding.injective (by simp [hu])
    simpa only [hxu] using ho
  have : Finite (f.fiber y) :=
    Finite.of_finite_univ isCompact_univ.finite_of_discrete
  simpa [Scheme.Hom.range_fiberι] using Set.finite_univ.image (f.fiberι y)

/-- Stalk isomorphy away from the centre gives quasi-finiteness of the
normalized Rees structural map at every point there. -/
theorem normalizedReesProjToSpec_quasiFiniteAt_offCentre
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (w : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      Palomar.normalization (reesProj I)))
    (hw : ¬ I ≤ (normalizedReesProjToSpec I a ha w).asIdeal) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    (normalizedReesProjToSpec I a ha).QuasiFiniteAt w := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  have hbij : Function.Bijective (β.stalkMap w).hom :=
    normalizedReesToSpec_stalkMap_bijective I a ha w hw
  exact RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective _ hbij.surjective)

/-- Every fiber of the normalized Rees structural map over a point away
from the centre is finite. -/
theorem normalizedReesProjToSpec_finite_fiber_offCentre
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (y : Spec (.of R)) (hy : ¬ I ≤ y.asIdeal) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    ((normalizedReesProjToSpec I a ha) ⁻¹' {y}).Finite := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper β := by
    dsimp only [β, normalizedReesProjToSpec]
    infer_instance
  apply finite_preimage_singleton_of_quasiFiniteAt_on_fiber β y
  intro w hw
  apply normalizedReesProjToSpec_quasiFiniteAt_offCentre I a ha w
  simpa only [β, hw] using hy

/-- Above any ambient point, there are only finitely many codimension-one
points of the normalized Rees blow-up outside the exceptional support. -/
theorem normalizedReesProjToSpec_finite_divisor_fiber_offExceptional
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (y : Spec (.of R)) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let β := normalizedReesProjToSpec I a ha
    let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
      {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
    {D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) |
      D ∉ Exceptional ∧ β D.1 = y}.Finite := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
    {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
  change {D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) |
    D ∉ Exceptional ∧ β D.1 = y}.Finite
  by_cases hy : I ≤ y.asIdeal
  · have hempty :
        {D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) |
          D ∉ Exceptional ∧ β D.1 = y} = ∅ := by
      ext D
      constructor
      · intro hD
        exfalso
        apply hD.1
        have hsupport := normalizedReesExceptionalIdealSheaf_support I a ha
        have hiff := Set.ext_iff.mp hsupport D.1
        apply hiff.mpr
        exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (hD.2 ▸ hy)
      · intro hD
        simp at hD
    rw [hempty]
    exact Set.finite_empty
  · have hfiber := normalizedReesProjToSpec_finite_fiber_offCentre
      k I hI a ha y hy
    apply Set.Finite.of_injOn
      (s := {D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) |
        D ∉ Exceptional ∧ β D.1 = y})
      (t := β ⁻¹' {y}) (f := fun D => D.1)
    · intro D hD
      exact hD.2
    · intro D _ E _ hDE
      exact Subtype.ext hDE
    · exact hfiber

/-- The actual normalized Rees target has a finite union of branch divisor
families as soon as every off-exceptional branch point maps into one fixed
finite ambient family. The finite-fiber condition is now discharged. -/
theorem normalizedRees_lifted_branch_family_finite
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (Ambient : Set (Spec (.of R))) (hAmbient : Ambient.Finite)
    (branch :
      (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
       ℕ → Set (SchemeDivisorPoint (Palomar.normalization (reesProj I)))))
    (hbranch :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let β := normalizedReesProjToSpec I a ha
      let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
        {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
      ∀ n D, D ∈ branch n → D ∈ Exceptional ∨ β D.1 ∈ Ambient) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (⋃ n, branch n).Finite) := by
  exact normalizedRees_lifted_branch_family_finite_of_finiteFibers
    k I hI a ha Ambient hAmbient
    (fun y _ => normalizedReesProjToSpec_finite_divisor_fiber_offExceptional
      k I hI a ha y) branch hbranch

#print axioms finite_preimage_singleton_of_quasiFiniteAt_on_fiber
#print axioms normalizedReesProjToSpec_quasiFiniteAt_offCentre
#print axioms normalizedReesProjToSpec_finite_fiber_offCentre
#print axioms normalizedReesProjToSpec_finite_divisor_fiber_offExceptional
#print axioms normalizedRees_lifted_branch_family_finite

end
end Pcf.Bounding.AllCodimBlowup
