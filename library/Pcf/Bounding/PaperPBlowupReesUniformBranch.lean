/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupPointClosureUniform
public import Pcf.Bounding.PaperPBlowupConstructionAffine

/-!
# The uniform branch bound for an affine normalized Rees square

This instantiates the point-closure branch bound with the actual finite
normalized Rees lift. It is the affine geometric specialization used in
`paper-p.tex`, Proposition `prop:bound-blowup`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
-- This Rees-square specialization synthesizes finiteness instances at four corners.
/-- A fixed exceptional target component of the actual normalized Rees
blow-up has a finite exceptional branch set on its normalized base image.
The upper component is the reduced closure of a point of the normalized
source blow-up. -/
theorem exists_finite_bad_for_normalizedRees_pointClosure_square
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [IsNormalScheme (Spec (.of R))]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (x : (let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) :=
        reesProj_isIntegral (I.map f) b hb
      Palomar.normalization (reesProj (I.map f))))
    (hmono :
      let φ := Spec.map (CommRingCat.ofHom f)
      letI : IsFinite φ := affineSpecMap_isFinite f hfin
      letI : IsDominant φ := affineSpecMap_isDominant f hf
      IsPrimeToPMonodromyMap p φ) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
    letI : Algebra.FiniteType k S :=
      RingHom.finiteType_algebraMap.mp
        (hfin.to_finiteType.comp
          (RingHom.finiteType_algebraMap.mpr inferInstance))
    let F := normalizedReesProjMap f hf hfin I a ha
    let α := normalizedReesProjToSpec (I.map f) b hb
    let β := normalizedReesProjToSpec I a ha
    let φ := Spec.map (CommRingCat.ofHom f)
    letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
    letI : IsFinite φ := affineSpecMap_isFinite f hfin
    letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
      reesProj_absoluteNormalizationMap_isFinite k I hI a ha
    letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) := by
      letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
      letI : Algebra.FiniteType k S :=
        RingHom.finiteType_algebraMap.mp
          (hfin.to_finiteType.comp
            (RingHom.finiteType_algebraMap.mpr inferInstance))
      exact reesProj_absoluteNormalizationMap_isFinite k (I.map f)
        (Ideal.FG.map hI f) b hb
    letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
    letI : IsProper (reesProjToSpec (I.map f)) :=
      reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
    letI : IsProper α := by dsimp only [α, normalizedReesProjToSpec]; infer_instance
    letI : IsProper β := by dsimp only [β, normalizedReesProjToSpec]; infer_instance
    let y := F x
    let z := β y
    let q := pointClosureSubschemeMap β y z rfl
    let u₀ := pointClosureSubschemeMap F x y rfl
    let hφ : φ (α x) = z := by
      have h := congrArg (fun m => m x)
        (normalizedReesProjToSpec_comm f hf hfin I a ha)
      simpa only [Scheme.Hom.comp_apply] using h.symm
    let g₀ := pointClosureSubschemeMap φ (α x) z hφ
    letI : IsDominant q := pointClosureSubschemeMap_isDominant _ _ _ _
    letI : IsDominant u₀ := pointClosureSubschemeMap_isDominant _ _ _ _
    letI : IsDominant g₀ := pointClosureSubschemeMap_isDominant _ _ _ _
    letI : IsFinite (Palomar.normalizationMap
      (pointClosureIdealSheaf x).subscheme) := by
      letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
      letI : Algebra.FiniteType k S :=
        RingHom.finiteType_algebraMap.mp
          (hfin.to_finiteType.comp
            (RingHom.finiteType_algebraMap.mpr inferInstance))
      letI : LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.finiteType_algebraMap.mpr inferInstance
      letI : LocallyOfFiniteType
          ((pointClosureIdealSheaf x).subschemeι ≫ α ≫
            Spec.map (CommRingCat.ofHom (algebraMap k S))) := inferInstance
      exact schemeGlobalNormalizationMap_isFinite
        (pointClosureIdealSheaf x).subscheme k
        ((pointClosureIdealSheaf x).subschemeι ≫ α ≫
          Spec.map (CommRingCat.ofHom (algebraMap k S)))
    letI : IsFinite (Palomar.normalizationMap
      (pointClosureIdealSheaf (α x)).subscheme) := by
      letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
      letI : Algebra.FiniteType k S :=
        RingHom.finiteType_algebraMap.mp
          (hfin.to_finiteType.comp
            (RingHom.finiteType_algebraMap.mpr inferInstance))
      letI : LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.finiteType_algebraMap.mpr inferInstance
      letI : LocallyOfFiniteType
          ((pointClosureIdealSheaf (α x)).subschemeι ≫
            Spec.map (CommRingCat.ofHom (algebraMap k S))) := inferInstance
      exact schemeGlobalNormalizationMap_isFinite
        (pointClosureIdealSheaf (α x)).subscheme k
        ((pointClosureIdealSheaf (α x)).subschemeι ≫
          Spec.map (CommRingCat.ofHom (algebraMap k S)))
    letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
    letI : IsLocallyNoetherian (Spec (.of S)) := inferInstance
    letI : IsLocallyNoetherian
      (pointClosureIdealSheaf (α x)).subscheme := inferInstance
    letI : IsLocallyNoetherian
      (Palomar.normalization (pointClosureIdealSheaf (α x)).subscheme) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (Palomar.normalizationMap (pointClosureIdealSheaf (α x)).subscheme)
    letI : IsFinite (Palomar.normalizationMap
      (pointClosureIdealSheaf z).subscheme) := by
      letI : LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.finiteType_algebraMap.mpr inferInstance
      letI : LocallyOfFiniteType
          ((pointClosureIdealSheaf z).subschemeι ≫
            Spec.map (CommRingCat.ofHom (algebraMap k R))) := inferInstance
      exact schemeGlobalNormalizationMap_isFinite
        (pointClosureIdealSheaf z).subscheme k
        ((pointClosureIdealSheaf z).subschemeι ≫
          Spec.map (CommRingCat.ofHom (algebraMap k R)))
    letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
    letI : IsLocallyNoetherian (pointClosureIdealSheaf z).subscheme := inferInstance
    letI : IsLocallyNoetherian
      (Palomar.normalization (pointClosureIdealSheaf z).subscheme) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (Palomar.normalizationMap (pointClosureIdealSheaf z).subscheme)
    letI : IsFinite u₀ := pointClosureSubschemeMap_isFinite _ _ _ _
    letI : IsFinite g₀ := pointClosureSubschemeMap_isFinite _ _ _ _
    letI : IsFinite (Palomar.normalizationMap
      (Palomar.normalization (pointClosureIdealSheaf (α x)).subscheme)) := by
      letI : IsIso (Palomar.normalizationMap
        (Palomar.normalization (pointClosureIdealSheaf (α x)).subscheme)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    letI : IsFinite (Palomar.normalizationMap
      (Palomar.normalization (pointClosureIdealSheaf z).subscheme)) := by
      letI : IsIso (Palomar.normalizationMap
        (Palomar.normalization (pointClosureIdealSheaf z).subscheme)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    ∃ Bad : Set (Palomar.normalization (pointClosureIdealSheaf z).subscheme),
      Bad.Finite ∧
      ∀ D : SchemeDivisorPoint
        (Palomar.normalization (pointClosureIdealSheaf z).subscheme),
        D.1 ∉ Bad →
        (∀ e : SchemeDivisorPoint
          (Palomar.normalization (pointClosureIdealSheaf x).subscheme),
          (schemeDominantNormalizationMorphism q)
            ((schemeDominantNormalizationMorphism u₀) e.1) = D.1 →
          ((schemeDominantNormalizationMorphism u₀).stalkMap e.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet (schemeDominantNormalizationMorphism g₀) := by
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  have hFT : (f.comp (algebraMap k R)).FiniteType :=
    hfin.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType k S := RingHom.finiteType_algebraMap.mp hFT
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let F := normalizedReesProjMap f hf hfin I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  let β := normalizedReesProjToSpec I a ha
  let φ := Spec.map (CommRingCat.ofHom f)
  letI : IsFinite φ := affineSpecMap_isFinite f hfin
  letI : IsDominant φ := affineSpecMap_isDominant f hf
  letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map f) (Ideal.FG.map hI f) b hb
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper (reesProjToSpec (I.map f)) :=
    reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
  letI : IsProper α := by dsimp only [α, normalizedReesProjToSpec]; infer_instance
  letI : IsProper β := by dsimp only [β, normalizedReesProjToSpec]; infer_instance
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : NoetherianSpace (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian (Spec (.of S)) := inferInstance
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec I)
  letI : IsLocallyNoetherian (reesProj (I.map f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec (I.map f))
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj I)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap (reesProj I))
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj (I.map f))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Palomar.normalizationMap (reesProj (I.map f)))
  let sX : Spec (.of S) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k S))
  let sY : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : LocallyOfFiniteType sX := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : LocallyOfFiniteType sY := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hsquare := normalizedReesProjToSpec_comm f hf hfin I a ha
  exact exists_finite_bad_for_pointClosure_square p k sX sY φ F α β hsquare x hmono

#print axioms exists_finite_bad_for_normalizedRees_pointClosure_square

end
end Pcf.Bounding.AllCodimBlowup
