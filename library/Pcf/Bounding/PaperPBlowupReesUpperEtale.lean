/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingCharPPointwise
public import Pcf.Bounding.PaperPBlowupActualSourceBound

/-!
# Bounding theorem on an actual normalized Rees component

This specializes the pointwise bounding theorem to the finite normalized
Rees lift. It turns avoidance of the manuscript's exact `Σ` for a target
component into the universal upper étaleness premise of the blow-up bound.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
-- The next proof builds the finite-type instances for a normalized Rees lift.
/-- The exact `thm:bounding` exceptional set gives upper point-closure
étaleness on the actual normalized Rees finite map in characteristic `p`. -/
theorem normalizedRees_upper_pointClosure_formallyEtale_of_notSigma
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
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
      SchemeDivisorPoint (Palomar.normalization (reesProj (I.map f))))) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    let X' := Palomar.normalization (reesProj (I.map f))
    let Y' := Palomar.normalization (reesProj I)
    let F := normalizedReesProjMap f hf hfin I a ha
    letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
    letI : IsDominant F := normalizedReesProjMap_isDominant f hf hfin I a ha
    letI : IsLocallyNoetherian Y' := by
      letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
      letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
      letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
        reesProjToSpecField_locallyOfFiniteType k I hI
      letI : IsLocallyNoetherian (reesProj I) :=
        LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpecField (k := k) I)
      letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
        reesProj_absoluteNormalizationMap_isFinite k I hI a ha
      infer_instance
    let dY : SchemeDivisorPoint Y' := x.mapFiniteDominantNormal F
    let X₀ := (pointClosureIdealSheaf x.1).subscheme
    let Y₀ := (pointClosureIdealSheaf dY.1).subscheme
    let u := pointClosureSubschemeMap F x.1 (F x.1) rfl
    letI : IsLocallyNoetherian X' := by
      letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
      letI : Algebra.FiniteType k S :=
        RingHom.finiteType_algebraMap.mp
          (hfin.to_finiteType.comp
            (RingHom.finiteType_algebraMap.mpr inferInstance))
      letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
      letI : IsLocallyNoetherian (Spec (.of S)) := inferInstance
      letI : LocallyOfFiniteType (reesProjToSpecField (k := k) (I.map f)) :=
        reesProjToSpecField_locallyOfFiniteType k (I.map f) (Ideal.FG.map hI f)
      letI : IsLocallyNoetherian (reesProj (I.map f)) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (reesProjToSpecField (k := k) (I.map f))
      letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) := by
        exact reesProj_absoluteNormalizationMap_isFinite k (I.map f)
          (Ideal.FG.map hI f) b hb
      infer_instance
    letI : IsFinite (Palomar.normalizationMap X') := by
      letI : IsIso (Palomar.normalizationMap X') :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    letI : IsFinite (Palomar.normalizationMap Y') := by
      letI : IsIso (Palomar.normalizationMap Y') :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    ∀ D : SchemeDivisorPoint Y₀,
      D.1 ∉ paperPBoundingSigma F dY →
      ∀ E : SchemeDivisorPoint X₀,
        u E.1 = D.1 → (u.stalkMap E.1).hom.FormallyEtale := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let X' := Palomar.normalization (reesProj (I.map f))
  let Y' := Palomar.normalization (reesProj I)
  let F := normalizedReesProjMap f hf hfin I a ha
  letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant f hf hfin I a ha
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  letI : Algebra.FiniteType k S :=
    RingHom.finiteType_algebraMap.mp
      (hfin.to_finiteType.comp
        (RingHom.finiteType_algebraMap.mpr inferInstance))
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian (Spec (.of S)) := inferInstance
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map f)
      (Ideal.FG.map hI f) b hb
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper (reesProjToSpec (I.map f)) :=
    reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec I)
  letI : IsLocallyNoetherian (reesProj (I.map f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec (I.map f))
  letI : IsLocallyNoetherian X' := inferInstance
  letI : IsLocallyNoetherian Y' := inferInstance
  letI : NoetherianSpace X' :=
    normalizedReesProj_noetherianSpace k (I.map f) (Ideal.FG.map hI f) b hb
  letI : NoetherianSpace Y' := normalizedReesProj_noetherianSpace k I hI a ha
  letI : IsFinite (Palomar.normalizationMap X') := by
    letI : IsIso (Palomar.normalizationMap X') :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap Y') := by
    letI : IsIso (Palomar.normalizationMap Y') :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  let dY : SchemeDivisorPoint Y' := x.mapFiniteDominantNormal F
  let X₀ := (pointClosureIdealSheaf x.1).subscheme
  let Y₀ := (pointClosureIdealSheaf dY.1).subscheme
  let u := pointClosureSubschemeMap F x.1 (F x.1) rfl
  let β := normalizedReesProjToSpec I a ha
  let sR : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsProper β := by dsimp only [β, normalizedReesProjToSpec]; infer_instance
  let sY : Y' ⟶ Spec (.of k) := β ≫ sR
  letI : LocallyOfFiniteType sY := inferInstance
  have hmonoF : IsPrimeToPMonodromyMap p F :=
    normalizedReesProjMap_primeToPMonodromy k p f hf hfin I hI a ha hmono
  letI : IsFinite (Palomar.normalizationMap X') := by
    letI : IsIso (Palomar.normalizationMap X') := normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap Y') := by
    letI : IsIso (Palomar.normalizationMap Y') := normalScheme_normalizationMap_isIso _
    infer_instance
  dsimp only
  intro D hD E hE
  have h := Pcf.paperPBoundingCharP_at_formallyEtale
    p (Fact.out) k sY F hmonoF x E.1 D hE hD
  dsimp only [SchemeDivisorPoint.mapFiniteDominantNormal,
    SchemeDivisorPoint.closureMapFiniteDominantNormal] at h
  exact h

#print axioms normalizedRees_upper_pointClosure_formallyEtale_of_notSigma

end
end Pcf.Bounding.AllCodimBlowup
