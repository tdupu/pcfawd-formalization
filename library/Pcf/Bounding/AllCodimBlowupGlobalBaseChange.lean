/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeBaseChange

/-!
# Structural maps for relative Rees Proj base change

The structural morphism of the Rees Proj is described on each standard
chart by its zero-degree ring map. This is the scheme-level compatibility
needed to assemble the relative blow-up comparison.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory Polynomial

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Coefficientwise base change respects the structural map to the
degree-zero Rees piece. -/
theorem gradedReesMap_zeroMap (f : R →+* S) (I : Ideal R) (r : R) :
    gradedReesMap f I (reesGradeZeroMap I r).1 =
      (reesGradeZeroMap (I.map f) (f r)).1 := by
  apply Subtype.ext
  simp [reesGradeZeroMap, gradedReesMap_apply]

/-- On a standard affine chart, the structural morphism is the spectrum of
the map from the degree-zero Rees piece to its homogeneous localization. -/
theorem reesProjChartOpen_toSpec (I : Ideal R) (a : I) :
    reesProjChartOpen I a ≫ reesProjToSpec I =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (reesGrade I)
          (Submonoid.powers (reesDegreeOne I a))).comp (reesGradeZeroMap I))) := by
  unfold reesProjToSpec
  change Proj.awayι (reesGrade I) (reesDegreeOne I a)
      (reesDegreeOne_mem_grade I a) (by decide) ≫
        Proj.toSpecZero (reesGrade I) ≫
          Spec.map (CommRingCat.ofHom (reesGradeZeroMap I)) = _
  rw [← Category.assoc]
  rw [Proj.awayι_toSpecZero]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem fromZero_eq_away_mk {T : Type*} [CommRing T]
    (J : Ideal T) (b : J) (t : T) :
    HomogeneousLocalization.fromZeroRingHom (reesGrade J)
      (Submonoid.powers (reesDegreeOne J b)) (reesGradeZeroMap J t) =
    HomogeneousLocalization.Away.mk (reesGrade J)
      (reesDegreeOne_mem_grade J b) 0 (reesGradeZeroMap J t).1
      (by exact (reesGradeZeroMap J t).2) := by
  rfl

/-- The degree-zero chart map carries a coefficient from the source base
to its image in the target base. -/
theorem reesProjChartMap_zeroMap (f : R →+* S) (I : Ideal R)
    (a : I) (r : R) :
    reesProjChartMap f I a
      (HomogeneousLocalization.fromZeroRingHom (reesGrade I)
        (Submonoid.powers (reesDegreeOne I a)) (reesGradeZeroMap I r)) =
      HomogeneousLocalization.fromZeroRingHom (reesGrade (I.map f))
        (Submonoid.powers (reesDegreeOne (I.map f)
          (mappedCenterElement f I a)))
        (reesGradeZeroMap (I.map f) (f r)) := by
  rw [fromZero_eq_away_mk I a r, reesProjChartMap_mk]
  rw [fromZero_eq_away_mk (I.map f) (mappedCenterElement f I a) (f r)]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk]
  rw [gradedReesMap_zeroMap]

/-- The base-change map on standard Proj charts respects their structural
maps to the two affine bases. -/
theorem reesProjChartMap_toSpec (f : R →+* S) (I : Ideal R)
    (a : I) :
    Spec.map (CommRingCat.ofHom (reesProjChartMap f I a)) ≫
        reesProjChartOpen I a ≫ reesProjToSpec I =
      reesProjChartOpen (I.map f) (mappedCenterElement f I a) ≫
        reesProjToSpec (I.map f) ≫
          Spec.map (CommRingCat.ofHom f) := by
  rw [reesProjChartOpen_toSpec]
  rw [← Category.assoc, reesProjChartOpen_toSpec]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  congr 1
  apply RingHom.ext
  intro r
  exact reesProjChartMap_zeroMap f I a r

/-- Naturality of the zero-degree base map on a homogeneous localization
at an arbitrary Rees element. -/
theorem gradedReesMap_fromZero (f : R →+* S) (I : Ideal R)
    (s : reesAlgebra I) (r : R) :
    HomogeneousLocalization.Away.map (gradedReesMap f I) s
      (HomogeneousLocalization.fromZeroRingHom (reesGrade I)
        (Submonoid.powers s) (reesGradeZeroMap I r)) =
      HomogeneousLocalization.fromZeroRingHom (reesGrade (I.map f))
        (Submonoid.powers (gradedReesMap f I s))
        (reesGradeZeroMap (I.map f) (f r)) := by
  change (HomogeneousLocalization.map (gradedReesMap f I) _)
      (HomogeneousLocalization.mk
        (⟨0, reesGradeZeroMap I r, 1, Submonoid.one_mem _⟩ :
          HomogeneousLocalization.NumDenSameDeg (reesGrade I) (Submonoid.powers s))) =
      HomogeneousLocalization.mk
        (⟨0, reesGradeZeroMap (I.map f) (f r), 1, Submonoid.one_mem _⟩ :
          HomogeneousLocalization.NumDenSameDeg (reesGrade (I.map f))
            (Submonoid.powers (gradedReesMap f I s)))
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  · exact gradedReesMap_zeroMap f I r
  · apply Subtype.ext
    simp

/-- The global Rees Proj map respects the affine-base structural maps
after restriction to any standard positive-degree affine open. -/
theorem reesProjMap_toSpec_onAway (f : R →+* S) (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (s : reesAlgebra I) (hs : s ∈ reesGrade I n) :
    Proj.awayι (reesGrade (I.map f)) (gradedReesMap f I s)
        ((gradedReesMap f I).map_mem hs) hn ≫
        reesProjMap f I ≫ reesProjToSpec I =
      Proj.awayι (reesGrade (I.map f)) (gradedReesMap f I s)
        ((gradedReesMap f I).map_mem hs) hn ≫
        reesProjToSpec (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  change Proj.awayι (reesGrade (I.map f)) (gradedReesMap f I s)
      ((gradedReesMap f I).map_mem hs) hn ≫
      Proj.map (gradedReesMap f I) (gradedReesMap_irrelevant_le f I) ≫
      (Proj.toSpecZero (reesGrade I) ≫
        Spec.map (CommRingCat.ofHom (reesGradeZeroMap I))) =
    Proj.awayι (reesGrade (I.map f)) (gradedReesMap f I s)
      ((gradedReesMap f I).map_mem hs) hn ≫
      (Proj.toSpecZero (reesGrade (I.map f)) ≫
        Spec.map (CommRingCat.ofHom (reesGradeZeroMap (I.map f)))) ≫
        Spec.map (CommRingCat.ofHom f)
  rw [← Category.assoc, Proj.awayι_comp_map (gradedReesMap f I)
    (gradedReesMap_irrelevant_le f I) hn s hs]
  rw [Category.assoc]
  simp only [Proj.awayι_toSpecZero_assoc]
  conv_rhs => rw [← Category.assoc, Proj.awayι_toSpecZero_assoc]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  congr 1
  apply RingHom.ext
  intro r
  exact gradedReesMap_fromZero f I s r

/-- The global Rees Proj map lies over the affine base-change map. This
equality is established on Mathlib's positive-degree affine open cover. -/
theorem reesProjMap_toSpec (f : R →+* S) (I : Ideal R) :
    reesProjMap f I ≫ reesProjToSpec I =
      reesProjToSpec (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  refine (Proj.mapAffineOpenCover (gradedReesMap f I)
    (gradedReesMap_irrelevant_le f I)).openCover.hom_ext _ _ fun s => ?_
  convert reesProjMap_toSpec_onAway f I s.1.2 s.2.1 s.2.2 using 1 <;> rfl

/-- The canonical morphism from the blow-up of the extended center to the
base change of the original blow-up, using Mathlib's actual scheme pullback.
The preceding theorem supplies the required global compatibility square. -/
noncomputable def reesProjRelativeBaseChange (f : R →+* S) (I : Ideal R) :
    reesProj (I.map f) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I) :=
  Limits.pullback.lift (reesProjToSpec (I.map f)) (reesProjMap f I)
    (reesProjMap_toSpec f I).symm

theorem reesProjRelativeBaseChange_fst (f : R →+* S) (I : Ideal R) :
    reesProjRelativeBaseChange f I ≫
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I) =
        reesProjToSpec (I.map f) :=
  Limits.pullback.lift_fst ..

theorem reesProjRelativeBaseChange_snd (f : R →+* S) (I : Ideal R) :
    reesProjRelativeBaseChange f I ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I) =
        reesProjMap f I :=
  Limits.pullback.lift_snd ..

#print axioms gradedReesMap_zeroMap
#print axioms reesProjChartOpen_toSpec
#print axioms reesProjChartMap_zeroMap
#print axioms reesProjChartMap_toSpec
#print axioms gradedReesMap_fromZero
#print axioms reesProjMap_toSpec_onAway
#print axioms reesProjMap_toSpec
#print axioms reesProjRelativeBaseChange
#print axioms reesProjRelativeBaseChange_fst
#print axioms reesProjRelativeBaseChange_snd

end Pcf.Bounding.AllCodimBlowup
