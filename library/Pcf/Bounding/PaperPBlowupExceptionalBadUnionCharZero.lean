/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupReesOriginalUniformCharZero

/-!
# A single ambient correction for all exceptional Rees components

The normalized blow-up of a fixed affine centre has finitely many exceptional
divisor generic points. Each such point carries the finite characteristic-zero branch correction
of `exists_finite_bad_for_fixed_normalizedRees_component`. This file takes the
finite union of their images in the original affine target.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The finite corrections for all exceptional components of one fixed
normalized Rees blow-up have a finite union in its original affine base. -/
theorem exists_finite_ambient_bad_for_exceptional_Rees_components_charZero
    (k : Type u) [Field k] [CharZero k]
    {R : Type u} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let β := normalizedReesProjToSpec I a ha
    let selectedBad : (dY : SchemeDivisorPoint (Palomar.normalization (reesProj I))) →
        Set (pointClosureIdealSheaf (β dY.1)).subscheme :=
      fun dY => Classical.choose
        (exists_finite_bad_for_fixed_normalizedRees_component_charZero k I hI a ha dY)
    ∃ Bad : Set (Spec (.of R)), Bad.Finite ∧
      ∀ dY : SchemeDivisorPoint (Palomar.normalization (reesProj I)),
        dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support →
        (pointClosureIdealSheaf (β dY.1)).subschemeι '' selectedBad dY ⊆ Bad := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  let selectedBad : (dY : SchemeDivisorPoint (Palomar.normalization (reesProj I))) →
      Set (pointClosureIdealSheaf (β dY.1)).subscheme :=
    fun dY => Classical.choose
      (exists_finite_bad_for_fixed_normalizedRees_component_charZero k I hI a ha dY)
  have hselectedFinite (dY : SchemeDivisorPoint (Palomar.normalization (reesProj I))) :
      (selectedBad dY).Finite :=
    (Classical.choose_spec
      (exists_finite_bad_for_fixed_normalizedRees_component_charZero k I hI a ha dY)).1
  let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
    {dY | dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
  have hExceptional : Exceptional.Finite :=
    normalizedReesExceptional_divisorPoints_finite k I hI a ha
  let Bad : Set (Spec (.of R)) :=
    ⋃ dY ∈ Exceptional,
      (pointClosureIdealSheaf (β dY.1)).subschemeι '' selectedBad dY
  have hBad : Bad.Finite := hExceptional.biUnion fun dY _ =>
    (hselectedFinite dY).image _
  refine ⟨Bad, hBad, ?_⟩
  intro dY hdY z hz
  exact Set.mem_biUnion hdY hz

#print axioms exists_finite_ambient_bad_for_exceptional_Rees_components_charZero

set_option maxHeartbeats 800000 in
-- The next theorem elaborates a dependent family of actual component squares.
/-- One finite subset of the original affine target excludes weighted branch
for every compatible finite/proper component square over every exceptional
component of the fixed normalized Rees blow-up. The square and upper étaleness
hypotheses can be supplied by the actual source point-closure construction. -/
theorem exists_finite_ambient_bad_for_all_exceptional_Rees_squares_charZero
    (k : Type u) [Field k] [CharZero k]
    {R : Type u} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let β := normalizedReesProjToSpec I a ha
    let sR : Spec (.of R) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k R))
    letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
    ∃ Bad : Set (Spec (.of R)), Bad.Finite ∧
      ∀ dY : SchemeDivisorPoint (Palomar.normalization (reesProj I)),
        dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support →
        let Y₀ := (pointClosureIdealSheaf dY.1).subscheme
        let Z₀ := (pointClosureIdealSheaf (β dY.1)).subscheme
        let q := pointClosureSubschemeMap β dY.1 (β dY.1) rfl
        letI : IsLocallyNoetherian Z₀ := inferInstance
        letI : LocallyOfFiniteType
            ((pointClosureIdealSheaf (β dY.1)).subschemeι ≫ sR) := by
          letI : LocallyOfFiniteType sR := by
            rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
            exact RingHom.finiteType_algebraMap.mpr inferInstance
          infer_instance
        letI : IsFinite (Palomar.normalizationMap Z₀) :=
          schemeGlobalNormalizationMap_isFinite Z₀ k
            ((pointClosureIdealSheaf (β dY.1)).subschemeι ≫ sR)
        ∀ {X W : Scheme.{u}}
          [IsIntegral X] [IsIntegral W]
          [IsLocallyNoetherian X] [IsLocallyNoetherian W]
          [IsFinite (Palomar.normalizationMap X)]
          [IsFinite (Palomar.normalizationMap W)]
          (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
          (F : X ⟶ Y₀) [IsFinite F] [IsDominant F]
          (v : X ⟶ W) [IsProper v] [IsDominant v]
          (g : W ⟶ Z₀) [IsFinite g] [IsDominant g]
          (_hsquare : F ≫ q = v ≫ g)
          (D : SchemeDivisorPoint Z₀),
          (pointClosureIdealSheaf (β dY.1)).subschemeι D.1 ∉ Bad →
          (∀ E : SchemeDivisorPoint X,
            q (F E.1) = D.1 → (F.stalkMap E.1).hom.FormallyEtale) →
          D.1 ∉ weightedBranchPointSet g := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  let sR : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  obtain ⟨Bad, hBad, hcover⟩ :=
    exists_finite_ambient_bad_for_exceptional_Rees_components_charZero k I hI a ha
  refine ⟨Bad, hBad, ?_⟩
  intro dY hdY
  let Y₀ := (pointClosureIdealSheaf dY.1).subscheme
  let Z₀ := (pointClosureIdealSheaf (β dY.1)).subscheme
  let q := pointClosureSubschemeMap β dY.1 (β dY.1) rfl
  letI : IsLocallyNoetherian Z₀ := inferInstance
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : LocallyOfFiniteType
      ((pointClosureIdealSheaf (β dY.1)).subschemeι ≫ sR) := inferInstance
  letI : IsFinite (Palomar.normalizationMap Z₀) :=
    schemeGlobalNormalizationMap_isFinite Z₀ k
      ((pointClosureIdealSheaf (β dY.1)).subschemeι ≫ sR)
  dsimp only
  intro X W _ _ _ _ _ _ sX _ F _ _ v _ _ g _ _ hsquare D hD heta
  have hselected := Classical.choose_spec
    (exists_finite_bad_for_fixed_normalizedRees_component_charZero k I hI a ha dY)
  have houtside : D.1 ∉ Classical.choose
      (exists_finite_bad_for_fixed_normalizedRees_component_charZero k I hI a ha dY) := by
    intro hmem
    exact hD (hcover dY hdY ⟨D.1, hmem, rfl⟩)
  exact hselected.2 sX F v g hsquare D houtside heta

#print axioms exists_finite_ambient_bad_for_all_exceptional_Rees_squares_charZero

end
end Pcf.Bounding.AllCodimBlowup
