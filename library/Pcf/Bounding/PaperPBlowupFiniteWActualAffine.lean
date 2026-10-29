/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupFiniteW

/-!
# The fixed finite branch family for actual affine normalized Rees lifts

This packages the finite family `W` for a sequence of finite normal affine
covers of one normal affine base. The only family premise is a finite ambient
set containing the original covers' divisor branch images.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- A finite dominant affine cover of a normal domain by a normal domain. -/
structure NormalAffineFiniteCover (R : Type u) [CommRing R] where
  S : Type u
  [commRing : CommRing S]
  [domain : IsDomain S]
  [integrallyClosed : IsIntegrallyClosed S]
  f : R →+* S
  injective : Function.Injective f
  finite : f.Finite

attribute [instance] NormalAffineFiniteCover.commRing NormalAffineFiniteCover.domain
  NormalAffineFiniteCover.integrallyClosed

/-- The original affine morphism belonging to a packaged finite cover. -/
def NormalAffineFiniteCover.specMap {R : Type u} [CommRing R]
    (C : NormalAffineFiniteCover R) : Spec (.of C.S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom C.f)

/-- The actual normalized Rees source for a packaged affine cover. -/
def NormalAffineFiniteCover.normalizedReesSource
    {R : Type u} [CommRing R] [IsDomain R]
    (C : NormalAffineFiniteCover R) (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    Scheme.{u} := by
  let b : I.map C.f := mappedCenterElement C.f I a
  have hb : (b : C.S) ≠ 0 := mappedCenterElement_ne_zero C.f C.injective I a ha
  letI : IsIntegral (reesProj (I.map C.f)) := reesProj_isIntegral (I.map C.f) b hb
  exact Palomar.normalization (reesProj (I.map C.f))

/-- The actual finite map of normalized Rees blow-ups for a packaged affine
cover. -/
def NormalAffineFiniteCover.normalizedReesLift
    {R : Type u} [CommRing R] [IsDomain R]
    (C : NormalAffineFiniteCover R) (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    C.normalizedReesSource I a ha ⟶
      (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
       Palomar.normalization (reesProj I)) := by
  exact normalizedReesProjMap C.f C.injective C.finite I a ha

set_option maxHeartbeats 800000 in
/-- One finite set of target branch generic points contains the branch
images of every actual normalized Rees lift in a sequence of finite normal
affine covers. -/
theorem NormalAffineFiniteCover.normalizedRees_branchImages_finite
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (Ambient : Set (Spec (.of R))) (hAmbient : Ambient.Finite)
    (hbranch : ∀ n, schemeDivisorBranchImage (C n).specMap ⊆ Ambient) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (⋃ n, schemeDivisorBranchImage ((C n).normalizedReesLift I a ha)).Finite) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  apply normalizedRees_actual_branch_images_finite k I hI a ha Ambient hAmbient
    (fun n => (C n).normalizedReesSource I a ha)
    (fun n => by
      let Cn := C n
      let b : I.map Cn.f := mappedCenterElement Cn.f I a
      have hb : (b : Cn.S) ≠ 0 :=
        mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
      letI : IsIntegral (reesProj (I.map Cn.f)) :=
        reesProj_isIntegral (I.map Cn.f) b hb
      change IsIntegral (Palomar.normalization (reesProj (I.map Cn.f)))
      infer_instance)
    (fun n => (C n).normalizedReesLift I a ha)
  · intro n
    let Cn := C n
    letI : Algebra k Cn.S := (Cn.f.comp (algebraMap k R)).toAlgebra
    letI : Algebra.FiniteType k Cn.S :=
      RingHom.finiteType_algebraMap.mp
        (Cn.finite.to_finiteType.comp
          (RingHom.finiteType_algebraMap.mpr inferInstance))
    exact normalizedReesProjMap_isFinite k Cn.f Cn.injective Cn.finite I hI a ha
  · intro n
    exact normalizedReesProjMap_isDominant (C n).f (C n).injective
      (C n).finite I a ha
  · dsimp only
    intro n y hy
    by_cases he : y ∈ (normalizedReesExceptionalIdealSheaf I a ha).support
    · exact Or.inl he
    · exact Or.inr
        (normalizedReesProjMap_branchImage_offExceptional
          (C n).f (C n).injective (C n).finite I a ha Ambient
          (hbranch n) y hy he)

/-- The PCF condition on the original affine covers is precisely a finite
union of their divisor branch images. It supplies the ambient finite set
without a separately chosen bound. -/
theorem NormalAffineFiniteCover.normalizedRees_branchImages_finite_of_pcf
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (hpcf : (⋃ n, schemeDivisorBranchImage (C n).specMap).Finite) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (⋃ n, schemeDivisorBranchImage ((C n).normalizedReesLift I a ha)).Finite) := by
  exact NormalAffineFiniteCover.normalizedRees_branchImages_finite
    k I hI a ha C _ hpcf
      (fun n => Set.subset_iUnion
        (fun m => schemeDivisorBranchImage (C m).specMap) n)

/-- The manuscript's fixed `W` on the affine normalized Rees target:
exceptional divisor generic points together with every lifted branch image. -/
def NormalAffineFiniteCover.normalizedReesTowerW
    {R : Type u} [CommRing R] [IsDomain R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     Set (Palomar.normalization (reesProj I))) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  exact (fun D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) => D.1) ''
      {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support} ∪
    ⋃ n, schemeDivisorBranchImage ((C n).normalizedReesLift I a ha)

/-- Every level's lifted branch image is contained in the fixed `W`. -/
theorem NormalAffineFiniteCover.branchImage_subset_normalizedReesTowerW
    {R : Type u} [CommRing R] [IsDomain R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R) (n : ℕ) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     schemeDivisorBranchImage ((C n).normalizedReesLift I a ha) ⊆
       normalizedReesTowerW I a ha C) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  intro y hy
  change y ∈
    (fun D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) => D.1) ''
      {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support} ∪
    ⋃ m, schemeDivisorBranchImage ((C m).normalizedReesLift I a ha)
  exact Or.inr (Set.mem_iUnion.mpr ⟨n, hy⟩)

/-- PCF of the original affine cover family makes the fixed `W` finite. -/
theorem NormalAffineFiniteCover.normalizedReesTowerW_finite_of_pcf
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (hpcf : (⋃ n, schemeDivisorBranchImage (C n).specMap).Finite) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (normalizedReesTowerW I a ha C).Finite) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  change ((fun D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) => D.1) ''
      {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support} ∪
    ⋃ n, schemeDivisorBranchImage ((C n).normalizedReesLift I a ha)).Finite
  exact (normalizedReesExceptional_divisorPoints_finite k I hI a ha).image _ |>.union
    (normalizedRees_branchImages_finite_of_pcf k I hI a ha C hpcf)

/-- Every generic point in `W` is a codimension-one point of the fixed
normalized Rees target. -/
theorem NormalAffineFiniteCover.normalizedReesTowerW_coheight_one
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (y : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      Palomar.normalization (reesProj I)))
    (hy : y ∈ normalizedReesTowerW I a ha C) :
    Order.coheight y = 1 := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  change y ∈
    (fun D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) => D.1) ''
      {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support} ∪
    ⋃ n, schemeDivisorBranchImage ((C n).normalizedReesLift I a ha) at hy
  rcases hy with ⟨D, -, rfl⟩ | hy
  · exact D.2
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    let Cn := C n
    letI : Algebra k Cn.S := (Cn.f.comp (algebraMap k R)).toAlgebra
    letI : Algebra.FiniteType k Cn.S :=
      RingHom.finiteType_algebraMap.mp
        (Cn.finite.to_finiteType.comp
          (RingHom.finiteType_algebraMap.mpr inferInstance))
    letI : IsFinite (Cn.normalizedReesLift I a ha) :=
      normalizedReesProjMap_isFinite k Cn.f Cn.injective Cn.finite I hI a ha
    letI : IsDominant (Cn.normalizedReesLift I a ha) :=
      normalizedReesProjMap_isDominant Cn.f Cn.injective Cn.finite I a ha
    letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
      reesProj_absoluteNormalizationMap_isFinite k I hI a ha
    letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
    letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
    letI : IsLocallyNoetherian (reesProj I) :=
      LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec I)
    letI : IsLocallyNoetherian (Palomar.normalization (reesProj I)) :=
      LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap (reesProj I))
    let b : I.map Cn.f := mappedCenterElement Cn.f I a
    have hb : (b : Cn.S) ≠ 0 :=
      mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
    letI : IsIntegral (reesProj (I.map Cn.f)) :=
      reesProj_isIntegral (I.map Cn.f) b hb
    letI : IsIntegral (Cn.normalizedReesSource I a ha) := by
      change IsIntegral (Palomar.normalization (reesProj (I.map Cn.f)))
      infer_instance
    exact schemeDivisorBranchImage_coheight_one
      (Cn.normalizedReesLift I a ha) y hn

set_option maxHeartbeats 800000 in
/-- The manuscript's weighted branch generic points of one packaged affine
normalized Rees lift. -/
def NormalAffineFiniteCover.liftWeightedBranchSet
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : NormalAffineFiniteCover R) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     Set (Palomar.normalization (reesProj I))) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map C.f := mappedCenterElement C.f I a
  have hb : (b : C.S) ≠ 0 :=
    mappedCenterElement_ne_zero C.f C.injective I a ha
  letI : IsIntegral (reesProj (I.map C.f)) :=
    reesProj_isIntegral (I.map C.f) b hb
  letI : Algebra k C.S := (C.f.comp (algebraMap k R)).toAlgebra
  letI : Algebra.FiniteType k C.S :=
    RingHom.finiteType_algebraMap.mp
      (C.finite.to_finiteType.comp
        (RingHom.finiteType_algebraMap.mpr inferInstance))
  let F := C.normalizedReesLift I a ha
  letI : IsIntegral (C.normalizedReesSource I a ha) := by
    change IsIntegral (Palomar.normalization (reesProj (I.map C.f)))
    infer_instance
  letI : IsFinite F := normalizedReesProjMap_isFinite
    k C.f C.injective C.finite I hI a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant
    C.f C.injective C.finite I a ha
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsNoetherianRing C.S := Algebra.FiniteType.isNoetherianRing k C.S
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian (Spec (.of C.S)) := inferInstance
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map C.f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map C.f)
      (Ideal.FG.map hI C.f) b hb
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper (reesProjToSpec (I.map C.f)) :=
    reesProjToSpec_isProper (I.map C.f) (Ideal.FG.map hI C.f)
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec I)
  letI : IsLocallyNoetherian (reesProj (I.map C.f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec (I.map C.f))
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj I)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap (reesProj I))
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj (I.map C.f))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Palomar.normalizationMap (reesProj (I.map C.f)))
  letI : IsLocallyNoetherian (C.normalizedReesSource I a ha) := by
    change IsLocallyNoetherian (Palomar.normalization (reesProj (I.map C.f)))
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization (reesProj I))) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization (reesProj I))) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite
      (Palomar.normalizationMap (Palomar.normalization (reesProj (I.map C.f)))) := by
    letI : IsIso (Palomar.normalizationMap
      (Palomar.normalization (reesProj (I.map C.f)))) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (C.normalizedReesSource I a ha)) := by
    letI : IsIso (Palomar.normalizationMap (C.normalizedReesSource I a ha)) := by
      change IsIso (Palomar.normalizationMap
        (Palomar.normalization (reesProj (I.map C.f))))
      exact normalScheme_normalizationMap_isIso _
    infer_instance
  exact weightedBranchPointSet F

set_option maxHeartbeats 800000 in
/-- Every weighted branch generic point of every actual affine normalized
Rees lift lies in the fixed `W`. -/
theorem NormalAffineFiniteCover.liftWeightedBranchSet_subset_W
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R) (n : ℕ) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (C n).liftWeightedBranchSet k I hI a ha ⊆
       normalizedReesTowerW I a ha C) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let Cn := C n
  let b : I.map Cn.f := mappedCenterElement Cn.f I a
  have hb : (b : Cn.S) ≠ 0 :=
    mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
  letI : IsIntegral (reesProj (I.map Cn.f)) :=
    reesProj_isIntegral (I.map Cn.f) b hb
  letI : Algebra k Cn.S := (Cn.f.comp (algebraMap k R)).toAlgebra
  letI : Algebra.FiniteType k Cn.S :=
    RingHom.finiteType_algebraMap.mp
      (Cn.finite.to_finiteType.comp
        (RingHom.finiteType_algebraMap.mpr inferInstance))
  let F := Cn.normalizedReesLift I a ha
  letI : IsIntegral (Cn.normalizedReesSource I a ha) := by
    change IsIntegral (Palomar.normalization (reesProj (I.map Cn.f)))
    infer_instance
  letI : IsFinite F := normalizedReesProjMap_isFinite
    k Cn.f Cn.injective Cn.finite I hI a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant
    Cn.f Cn.injective Cn.finite I a ha
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsNoetherianRing Cn.S := Algebra.FiniteType.isNoetherianRing k Cn.S
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian (Spec (.of Cn.S)) := inferInstance
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map Cn.f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map Cn.f)
      (Ideal.FG.map hI Cn.f) b hb
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper (reesProjToSpec (I.map Cn.f)) :=
    reesProjToSpec_isProper (I.map Cn.f) (Ideal.FG.map hI Cn.f)
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec I)
  letI : IsLocallyNoetherian (reesProj (I.map Cn.f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec (I.map Cn.f))
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj I)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap (reesProj I))
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj (I.map Cn.f))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Palomar.normalizationMap (reesProj (I.map Cn.f)))
  letI : IsLocallyNoetherian (Cn.normalizedReesSource I a ha) := by
    change IsLocallyNoetherian (Palomar.normalization (reesProj (I.map Cn.f)))
    infer_instance
  letI : IsNormalScheme (Cn.normalizedReesSource I a ha) := by
    change IsNormalScheme (Palomar.normalization (reesProj (I.map Cn.f)))
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization (reesProj I))) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization (reesProj I))) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite
      (Palomar.normalizationMap (Palomar.normalization (reesProj (I.map Cn.f)))) := by
    letI : IsIso (Palomar.normalizationMap
      (Palomar.normalization (reesProj (I.map Cn.f)))) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Cn.normalizedReesSource I a ha)) := by
    letI : IsIso (Palomar.normalizationMap (Cn.normalizedReesSource I a ha)) := by
      change IsIso (Palomar.normalizationMap
        (Palomar.normalization (reesProj (I.map Cn.f))))
      exact normalScheme_normalizationMap_isIso _
    infer_instance
  have hw : weightedBranchPointSet F ⊆ schemeDivisorBranchImage F :=
    weightedBranchPointSet_subset_schemeDivisorBranchImage F
  exact hw.trans (branchImage_subset_normalizedReesTowerW I a ha C n)

#print axioms NormalAffineFiniteCover.normalizedRees_branchImages_finite
#print axioms NormalAffineFiniteCover.normalizedRees_branchImages_finite_of_pcf
#print axioms NormalAffineFiniteCover.branchImage_subset_normalizedReesTowerW
#print axioms NormalAffineFiniteCover.normalizedReesTowerW_finite_of_pcf
#print axioms NormalAffineFiniteCover.normalizedReesTowerW_coheight_one
#print axioms NormalAffineFiniteCover.liftWeightedBranchSet_subset_W

end
end Pcf.Bounding.AllCodimBlowup
