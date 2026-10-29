/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupRestrictionMonodromy
public import Pcf.Bounding.GlobalNormalizationFinite

/-!
# Finite normalization of the two actual source point closures

The point closures in the actual normalized Rees component square are
Noetherian and of finite type over the ground field. Their normalization
maps are therefore finite over an arbitrary field, including imperfect
fields in positive characteristic.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The two reduced source closures in the actual Rees square have finite
normalization maps and are locally Noetherian. -/
theorem normalizedRees_source_pointClosures_finiteNormalization
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (x : (let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) :=
        reesProj_isIntegral (I.map f) b hb
      Palomar.normalization (reesProj (I.map f)))) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    let α := normalizedReesProjToSpec (I.map f) b hb
    let X₀ := (pointClosureIdealSheaf x).subscheme
    let W₀ := (pointClosureIdealSheaf (α x)).subscheme
    IsLocallyNoetherian X₀ ∧ IsLocallyNoetherian W₀ ∧
      IsFinite (Palomar.normalizationMap X₀) ∧
      IsFinite (Palomar.normalizationMap W₀) := by
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  have hFT : (f.comp (algebraMap k R)).FiniteType :=
    hfin.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType k S := RingHom.finiteType_algebraMap.mp hFT
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let α := normalizedReesProjToSpec (I.map f) b hb
  let X₀ := (pointClosureIdealSheaf x).subscheme
  let W₀ := (pointClosureIdealSheaf (α x)).subscheme
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsLocallyNoetherian (Spec (.of S)) := inferInstance
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map f)
      (Ideal.FG.map hI f) b hb
  letI : IsProper (reesProjToSpec (I.map f)) :=
    reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
  letI : IsLocallyNoetherian (reesProj (I.map f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec (I.map f))
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj (I.map f))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Palomar.normalizationMap (reesProj (I.map f)))
  letI : IsLocallyNoetherian X₀ := inferInstance
  letI : IsLocallyNoetherian W₀ := inferInstance
  let sS : Spec (.of S) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k S))
  letI : LocallyOfFiniteType sS := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsProper α := by dsimp only [α, normalizedReesProjToSpec]; infer_instance
  letI : LocallyOfFiniteType α := inferInstance
  letI : LocallyOfFiniteType ((pointClosureIdealSheaf x).subschemeι ≫ α ≫ sS) :=
    inferInstance
  letI : LocallyOfFiniteType ((pointClosureIdealSheaf (α x)).subschemeι ≫ sS) :=
    inferInstance
  exact ⟨inferInstance, inferInstance,
    schemeGlobalNormalizationMap_isFinite X₀ k
      ((pointClosureIdealSheaf x).subschemeι ≫ α ≫ sS),
    schemeGlobalNormalizationMap_isFinite W₀ k
      ((pointClosureIdealSheaf (α x)).subschemeι ≫ sS)⟩

#print axioms normalizedRees_source_pointClosures_finiteNormalization

end
end Pcf.Bounding.AllCodimBlowup
