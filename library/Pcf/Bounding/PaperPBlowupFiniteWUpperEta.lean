/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupFiniteWActualAffine
public import Pcf.Bounding.PaperPBoundingUniformUpperEtale

/-!
# The fixed affine tower family gives upper point-closure étaleness

The fixed finite set `W` constructed from the original PCF branch images
is inserted into `thm:bounding` for each actual normalized Rees lift.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
/-- In characteristic `p`, the fixed `W` gives one finite correction on the
target closure of every source divisor, and upper étaleness outside it. -/
theorem NormalAffineFiniteCover.upperEtale_of_fixedW_charP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (hpcf : (⋃ n, schemeDivisorBranchImage (C n).specMap).Finite)
    (n : ℕ)
    (hmono :
      let Cn := C n
      letI : IsFinite Cn.specMap := affineSpecMap_isFinite Cn.f Cn.finite
      letI : IsDominant Cn.specMap := affineSpecMap_isDominant Cn.f Cn.injective
      Pcf.IsPrimeToPMonodromyMap p Cn.specMap)
    (A : SchemeDivisorPoint ((C n).normalizedReesSource I a ha)) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let Cn := C n
    let b : I.map Cn.f := mappedCenterElement Cn.f I a
    let hb : (b : Cn.S) ≠ 0 :=
      mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
    letI : IsIntegral (reesProj (I.map Cn.f)) :=
      reesProj_isIntegral (I.map Cn.f) b hb
    let X' := Cn.normalizedReesSource I a ha
    let Y' := Palomar.normalization (reesProj I)
    let F := Cn.normalizedReesLift I a ha
    letI : IsIntegral X' := by
      change IsIntegral (Palomar.normalization (reesProj (I.map Cn.f)))
      infer_instance
    letI : IsLocallyNoetherian Y' := by
      letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
      letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
      letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
        reesProj_absoluteNormalizationMap_isFinite k I hI a ha
      letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
      letI : IsLocallyNoetherian (reesProj I) :=
        LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec I)
      infer_instance
    letI : IsFinite F := by
      letI : Algebra k Cn.S := (Cn.f.comp (algebraMap k R)).toAlgebra
      letI : Algebra.FiniteType k Cn.S :=
        RingHom.finiteType_algebraMap.mp
          (Cn.finite.to_finiteType.comp
            (RingHom.finiteType_algebraMap.mpr inferInstance))
      exact normalizedReesProjMap_isFinite k Cn.f Cn.injective Cn.finite I hI a ha
    letI : IsDominant F := normalizedReesProjMap_isDominant
      Cn.f Cn.injective Cn.finite I a ha
    let B := A.mapFiniteDominantNormal F
    let W := normalizedReesTowerW I a ha C
    {D : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
      D.1 ∈ Pcf.paperPBoundingFixedSigma W B}.Finite ∧
      ∀ D : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme,
        D.1 ∉ Pcf.paperPBoundingFixedSigma W B →
        ∀ E : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme,
          A.closureMapFiniteDominantNormal F E.1 = D.1 →
          ((A.closureMapFiniteDominantNormal F).stalkMap E.1).hom.FormallyEtale := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let Cn := C n
  let b : I.map Cn.f := mappedCenterElement Cn.f I a
  have hb : (b : Cn.S) ≠ 0 :=
    mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
  letI : IsIntegral (reesProj (I.map Cn.f)) :=
    reesProj_isIntegral (I.map Cn.f) b hb
  let X' := Cn.normalizedReesSource I a ha
  let Y' := Palomar.normalization (reesProj I)
  let F := Cn.normalizedReesLift I a ha
  let W := normalizedReesTowerW I a ha C
  letI : IsIntegral X' := by
    change IsIntegral (Palomar.normalization (reesProj (I.map Cn.f)))
    infer_instance
  letI : Algebra k Cn.S := (Cn.f.comp (algebraMap k R)).toAlgebra
  letI : Algebra.FiniteType k Cn.S :=
    RingHom.finiteType_algebraMap.mp
      (Cn.finite.to_finiteType.comp
        (RingHom.finiteType_algebraMap.mpr inferInstance))
  letI : IsFinite F := normalizedReesProjMap_isFinite
    k Cn.f Cn.injective Cn.finite I hI a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant
    Cn.f Cn.injective Cn.finite I a ha
  letI : IsFinite Cn.specMap := affineSpecMap_isFinite Cn.f Cn.finite
  letI : IsDominant Cn.specMap := affineSpecMap_isDominant Cn.f Cn.injective
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
  letI : IsLocallyNoetherian Y' := inferInstance
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj (I.map Cn.f))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Palomar.normalizationMap (reesProj (I.map Cn.f)))
  letI : IsLocallyNoetherian X' := by
    change IsLocallyNoetherian (Palomar.normalization (reesProj (I.map Cn.f)))
    infer_instance
  letI : IsNormalScheme X' := by
    change IsNormalScheme (Palomar.normalization (reesProj (I.map Cn.f)))
    infer_instance
  letI : NoetherianSpace Y' := normalizedReesProj_noetherianSpace k I hI a ha
  letI : NoetherianSpace X' := by
    change NoetherianSpace (Palomar.normalization (reesProj (I.map Cn.f)))
    exact normalizedReesProj_noetherianSpace
      k (I.map Cn.f) (Ideal.FG.map hI Cn.f) b hb
  letI : IsFinite (Palomar.normalizationMap X') := by
    letI : IsIso (Palomar.normalizationMap X') := normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap Y') := by
    letI : IsIso (Palomar.normalizationMap Y') := normalScheme_normalizationMap_isIso _
    infer_instance
  let β := normalizedReesProjToSpec I a ha
  let sR : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  let sY : Y' ⟶ Spec (.of k) := β ≫ sR
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsProper β := by
    dsimp only [β, normalizedReesProjToSpec]
    infer_instance
  letI : LocallyOfFiniteType sY := inferInstance
  have hmonoF : Pcf.IsPrimeToPMonodromyMap p F :=
    normalizedReesProjMap_primeToPMonodromy k p Cn.f Cn.injective
      Cn.finite I hI a ha hmono
  have hW : W.Finite := normalizedReesTowerW_finite_of_pcf
    k I hI a ha C hpcf
  have hWcodim : ∀ y ∈ W, Order.coheight y = 1 :=
    fun y hy => normalizedReesTowerW_coheight_one k I hI a ha C y hy
  have hbranchF : weightedBranchPointSet F ⊆ W := by
    change Cn.liftWeightedBranchSet k I hI a ha ⊆ W
    exact liftWeightedBranchSet_subset_W k I hI a ha C n
  exact Pcf.paperPBoundingCharP_upperEtale_of_fixedFamily
    p hp k sY F hmonoF A W hW hWcodim hbranchF

#print axioms NormalAffineFiniteCover.upperEtale_of_fixedW_charP

end
end Pcf.Bounding.AllCodimBlowup
