/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalNormalizedLift
public import Pcf.Bounding.PaperPTowerChartLocality

/-!
# Affine charts of the global normalized blow-up

Over a nonempty affine open `U = Spec R` of the target, the global normalized
blow-up restricts to the affine normalized Rees blow-up of `R` along `I(U)`:
the absolute normalization of the Rees chart is the Cartesian base change of
the global normalization map, and the global finite lift `f'` restricts to the
affine lift `normalizedReesProjMap` of the finite ring map `Γ(Y, U) ⟶ Γ(X, f⁻¹U)`.
This identifies the global construction of `latex/paper-p.tex`,
`prop:normalized-blowup-construction`, with the affine constructions used in
the chart proofs.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

/-- For a finite dominant morphism of integral schemes, the dominant
normalization morphism is the finite normalization morphism. -/
theorem schemeDominantNormalizationMorphism_eq_global {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [IsFinite π] [IsDominant π] :
    Pcf.schemeDominantNormalizationMorphism π = Pcf.schemeGlobalNormalizationMorphism π :=
  Pcf.schemeGlobalNormalizationMorphism_unique π _
    (Pcf.schemeDominantNormalizationMorphism_comp_normalizationMap π)
    (Pcf.schemeGenericToNormalization_dominantMorphism π)

variable {Y : Scheme.{u}} [IsIntegral Y] (I : Y.IdealSheafData)
  [hI : Fact (genericPoint Y ∉ I.support)]

/-- The normalized chart over a nonempty affine open is the base change of
the global normalization map along the Rees chart (scoped Stacks `035K`).

`paper-p.tex` correspondence: Proposition 7.7 (`prop:normalized-blowup-construction`). -/
theorem globalNormalizedBlowup_chart_isPullback (U : Y.affineOpens)
    (hU : (U.1 : Set Y).Nonempty) :
    letI := reesProj_isIntegral_of_nonempty I hI.out U hU
    IsPullback (Palomar.normalizationMap (reesProj (I.ideal U)))
      (Pcf.absoluteNormalizationOpenMap (globalReesChart I U))
      (globalReesChart I U) (Palomar.normalizationMap (globalRees I)) := by
  letI := reesProj_isIntegral_of_nonempty I hI.out U hU
  exact Pcf.absoluteNormalizationOpen_isPullback (globalReesChart I U)

/-- The normalized chart lies over the affine open through the affine
normalized Rees structure map. -/
theorem globalNormalizedBlowup_chart_toBase (U : Y.affineOpens) [Nonempty U.1] (a : I.ideal U)
    (ha : (a : Γ(Y, U.1)) ≠ 0) :
    letI : IsIntegral (reesProj (I.ideal U)) := reesProj_isIntegral (I.ideal U) a ha
    Pcf.absoluteNormalizationOpenMap (globalReesChart I U) ≫ globalNormalizedBlowupToBase I =
      normalizedReesProjToSpec (I.ideal U) a ha ≫ U.2.fromSpec := by
  letI : IsIntegral (reesProj (I.ideal U)) := reesProj_isIntegral (I.ideal U) a ha
  rw [globalNormalizedBlowupToBase, Pcf.absoluteNormalizationOpenMap_comp_assoc,
    globalReesChart_toBase']
  rfl

section Map

variable {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) [IsFinite f] [IsDominant f]

omit hI [IsFinite f] in
/-- The preimage of a nonempty open under a dominant morphism of integral
schemes is nonempty. -/
theorem preimage_nonempty_of_isDominant (U : Y.affineOpens) [Nonempty U.1] :
    Nonempty (f ⁻¹ᵁ U.1) := by
  obtain ⟨y⟩ := ‹Nonempty U.1›
  have hU : (U.1 : Set Y).Nonempty := ⟨y.1, y.2⟩
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U.1
  rw [map_genericPoint_eq_of_isDominant f]
  exact genericPoint_mem_affineOpen U hU

/-- The source chart of the global Rees map over an affine open of the
target, an open immersion from the extended affine Rees blow-up. -/
def globalReesSourceChart (U : Y.affineOpens) :
    reesProj (liftIdeal f I U) ⟶ globalRees (I.comap f) :=
  liftReesComparisonApp f I U ≫ globalReesChart (I.comap f) (preimageAffine f U)

instance globalReesSourceChart_isOpenImmersion (U : Y.affineOpens) :
    IsOpenImmersion (globalReesSourceChart I f U) := by
  dsimp only [globalReesSourceChart]
  infer_instance

omit [IsIntegral Y] hI [IsIntegral X] [IsDominant f] in
@[reassoc]
theorem globalReesSourceChart_map (U : Y.affineOpens) :
    globalReesSourceChart I f U ≫ globalReesMap f I =
      liftReesMapApp f I U ≫ globalReesChart I U := by
  rw [globalReesSourceChart, Category.assoc, globalReesChart_globalReesMap,
    IsIso.hom_inv_id_assoc]

/-- **Chart identification of the global normalized blow-up.** Over a nonempty
affine open `U` of `Y`, the global finite lift `f'` restricts to the affine
normalized Rees lift of `Γ(Y, U) ⟶ Γ(X, f⁻¹U)` along `I(U)`.

`paper-p.tex` correspondence: Proposition 7.7 (`prop:normalized-blowup-construction`), Definition
7.8 (`defn:normalized-blow-up`). -/
theorem globalNormalizedBlowupMap_chart (U : Y.affineOpens) [Nonempty U.1] (a : I.ideal U)
    (ha : (a : Γ(Y, U.1)) ≠ 0) (hinj : Function.Injective (f.app U.1).hom) :
    haveI := preimage_nonempty_of_isDominant f U
    letI : IsIntegral (reesProj (I.ideal U)) := reesProj_isIntegral (I.ideal U) a ha
    let b : (I.ideal U).map (f.app U.1).hom := mappedCenterElement (f.app U.1).hom (I.ideal U) a
    letI : IsIntegral (reesProj ((I.ideal U).map (f.app U.1).hom)) :=
      reesProj_isIntegral _ b (mappedCenterElement_ne_zero (f.app U.1).hom hinj (I.ideal U) a ha)
    normalizedReesProjMap (f.app U.1).hom hinj (f.finite_app U.1 U.2) (I.ideal U) a ha ≫
        Pcf.absoluteNormalizationOpenMap (globalReesChart I U) =
      Pcf.absoluteNormalizationOpenMap (globalReesSourceChart I f U) ≫
        globalNormalizedBlowupMap f I := by
  haveI := preimage_nonempty_of_isDominant f U
  letI : IsIntegral (reesProj (I.ideal U)) := reesProj_isIntegral (I.ideal U) a ha
  let b : (I.ideal U).map (f.app U.1).hom := mappedCenterElement (f.app U.1).hom (I.ideal U) a
  letI : IsIntegral (reesProj ((I.ideal U).map (f.app U.1).hom)) :=
    reesProj_isIntegral _ b (mappedCenterElement_ne_zero (f.app U.1).hom hinj (I.ideal U) a ha)
  letI : IsFinite (reesProjMap (f.app U.1).hom (I.ideal U)) :=
    reesProjMap_isFinite _ _ (f.finite_app U.1 U.2)
  letI : IsDominant (reesProjMap (f.app U.1).hom (I.ideal U)) :=
    reesProjMap_isDominant_of_injective _ hinj (I.ideal U) a ha
  dsimp only
  rw [globalNormalizedBlowupMap, schemeDominantNormalizationMorphism_eq_global]
  exact Pcf.schemeGlobalNormalizationMorphism_open_square
    (reesProjMap (f.app U.1).hom (I.ideal U)) (globalReesMap f I)
    (globalReesSourceChart I f U) (globalReesChart I U)
    (globalReesSourceChart_map I f U).symm

end Map

#print axioms globalNormalizedBlowup_chart_isPullback
#print axioms globalNormalizedBlowupMap_chart

end
end Pcf.Bounding.AllCodimBlowup
