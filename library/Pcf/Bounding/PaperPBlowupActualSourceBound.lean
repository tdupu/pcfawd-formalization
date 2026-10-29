/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupSourceClosureFinite
public import Pcf.Bounding.PaperPBlowupExceptionalBadUnion

/-!
# Branch bound for an actual affine normalized Rees source component

This applies the fixed exceptional-component correction to the actual four
point closures arising from a finite affine cover and normalized Rees lift.
The only mathematical premise left at this stage is étaleness of the upper
restricted finite map over the divisor in question.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
-- The next proof instantiates a dependent bound with four actual point closures.
/-- Outside one finite subset of the original affine target, upper component
étaleness excludes weighted branch of the actual lower point-closure map. -/
theorem exists_finite_bad_for_actual_affine_Rees_source_component
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [IsNormalScheme (Spec (.of R))]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (hmono :
      let φ := Spec.map (CommRingCat.ofHom f)
      letI : IsFinite φ := affineSpecMap_isFinite f hfin
      letI : IsDominant φ := affineSpecMap_isDominant f hf
      IsPrimeToPMonodromyMap p φ)
    (x : (let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) :=
        reesProj_isIntegral (I.map f) b hb
      SchemeDivisorPoint (Palomar.normalization (reesProj (I.map f)))))
    (hexceptional :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) :=
        reesProj_isIntegral (I.map f) b hb
      let F := normalizedReesProjMap f hf hfin I a ha
      F x.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    let F := normalizedReesProjMap f hf hfin I a ha
    let α := normalizedReesProjToSpec (I.map f) b hb
    let β := normalizedReesProjToSpec I a ha
    let φ := Spec.map (CommRingCat.ofHom f)
    letI : IsFinite φ := affineSpecMap_isFinite f hfin
    letI : IsDominant φ := affineSpecMap_isDominant f hf
    let hbase : φ (α x.1) = β (F x.1) := by
      have h := congrArg (fun m => m x.1)
        (normalizedReesProjToSpec_comm f hf hfin I a ha)
      simpa only [Scheme.Hom.comp_apply] using h.symm
    let X₀ := (pointClosureIdealSheaf x.1).subscheme
    let W₀ := (pointClosureIdealSheaf (α x.1)).subscheme
    let Z₀ := (pointClosureIdealSheaf (β (F x.1))).subscheme
    let u := pointClosureSubschemeMap F x.1 (F x.1) rfl
    let q := pointClosureSubschemeMap β (F x.1) (β (F x.1)) rfl
    let g := pointClosureSubschemeMap φ (α x.1) (β (F x.1)) hbase
    let hSource := normalizedRees_source_pointClosures_finiteNormalization
      k f hf hfin I hI a ha x.1
    letI : IsLocallyNoetherian W₀ := hSource.2.1
    letI : IsFinite (Palomar.normalizationMap W₀) := hSource.2.2.2
    let sR : Spec (.of R) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k R))
    letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
    letI : IsLocallyNoetherian Z₀ := inferInstance
    letI : LocallyOfFiniteType
        ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR) := by
      letI : LocallyOfFiniteType sR := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.finiteType_algebraMap.mpr inferInstance
      infer_instance
    letI : IsFinite (Palomar.normalizationMap Z₀) :=
      schemeGlobalNormalizationMap_isFinite Z₀ k
        ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR)
    letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
    letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
    ∃ Bad : Set (Spec (.of R)), Bad.Finite ∧
      ∀ D : SchemeDivisorPoint Z₀,
        (pointClosureIdealSheaf (β (F x.1))).subschemeι D.1 ∉ Bad →
        (∀ E : SchemeDivisorPoint X₀,
          q (u E.1) = D.1 → (u.stalkMap E.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet g := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let F := normalizedReesProjMap f hf hfin I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  let β := normalizedReesProjToSpec I a ha
  let φ := Spec.map (CommRingCat.ofHom f)
  have hbase : φ (α x.1) = β (F x.1) := by
    have h := congrArg (fun m => m x.1)
      (normalizedReesProjToSpec_comm f hf hfin I a ha)
    simpa only [Scheme.Hom.comp_apply] using h.symm
  let X₀ := (pointClosureIdealSheaf x.1).subscheme
  let W₀ := (pointClosureIdealSheaf (α x.1)).subscheme
  let Z₀ := (pointClosureIdealSheaf (β (F x.1))).subscheme
  let u := pointClosureSubschemeMap F x.1 (F x.1) rfl
  let v := pointClosureSubschemeMap α x.1 (α x.1) rfl
  let q := pointClosureSubschemeMap β (F x.1) (β (F x.1)) rfl
  let g := pointClosureSubschemeMap φ (α x.1) (β (F x.1)) hbase
  letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant f hf hfin I a ha
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
    reesProjToSpecField_locallyOfFiniteType k I hI
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpecField (k := k) I)
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj I)) := inferInstance
  let dY : SchemeDivisorPoint (Palomar.normalization (reesProj I)) :=
    x.mapFiniteDominantNormal F
  have hex : dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support :=
    hexceptional
  let hSource := normalizedRees_source_pointClosures_finiteNormalization
    k f hf hfin I hI a ha x.1
  letI : IsLocallyNoetherian X₀ := hSource.1
  letI : IsLocallyNoetherian W₀ := hSource.2.1
  letI : IsFinite (Palomar.normalizationMap X₀) := hSource.2.2.1
  letI : IsFinite (Palomar.normalizationMap W₀) := hSource.2.2.2
  letI : IsFinite u := pointClosureSubschemeMap_isFinite _ _ _ _
  letI : IsDominant u := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  letI : Algebra.FiniteType k S :=
    RingHom.finiteType_algebraMap.mp
      (hfin.to_finiteType.comp
        (RingHom.finiteType_algebraMap.mpr inferInstance))
  letI : IsProper (reesProjToSpec (I.map f)) :=
    reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map f)
      (Ideal.FG.map hI f) b hb
  letI : IsProper α := by dsimp only [α, normalizedReesProjToSpec]; infer_instance
  letI : IsProper v := pointClosureSubschemeMap_isProper _ _ _ _
  letI : IsDominant v := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsFinite φ := affineSpecMap_isFinite f hfin
  letI : IsDominant φ := affineSpecMap_isDominant f hf
  letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
  letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian Z₀ := inferInstance
  let sR : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : LocallyOfFiniteType
      ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR) := inferInstance
  letI : IsFinite (Palomar.normalizationMap Z₀) :=
    schemeGlobalNormalizationMap_isFinite Z₀ k
      ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR)
  let sS : Spec (.of S) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k S))
  letI : LocallyOfFiniteType sS := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map f)
      (Ideal.FG.map hI f) b hb
  letI : IsProper (reesProjToSpec (I.map f)) :=
    reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
  letI : IsProper α := by dsimp only [α, normalizedReesProjToSpec]; infer_instance
  let sX : X₀ ⟶ Spec (.of k) :=
    (pointClosureIdealSheaf x.1).subschemeι ≫ α ≫ sS
  letI : LocallyOfFiniteType sX := inferInstance
  have hsq := normalizedReesProjMap_pointClosure_square f hf hfin I a ha x.1
  have hmonog := normalizedRees_lower_pointClosure_primeToPMonodromy
    p k f hf hfin I a ha hmono x.1
  obtain ⟨Bad, hBad, hbound⟩ :=
    exists_finite_ambient_bad_for_all_exceptional_Rees_squares p k I hI a ha
  refine ⟨Bad, hBad, ?_⟩
  intro D hD heta
  have hboundY := hbound dY hex (X := X₀) (W := W₀)
  dsimp only [dY, SchemeDivisorPoint.mapFiniteDominantNormal] at hboundY
  exact hboundY sX u v g hsq hmonog D hD heta

#print axioms exists_finite_bad_for_actual_affine_Rees_source_component

end
end Pcf.Bounding.AllCodimBlowup
