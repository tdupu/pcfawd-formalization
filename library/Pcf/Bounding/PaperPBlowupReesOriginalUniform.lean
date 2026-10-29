/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupOriginalEtaleUniform
public import Pcf.Bounding.PaperPBlowupConstructionAffine

/-!
# One branch correction for a fixed normalized Rees component

Fix the target normalized blow-up and a component generic point. Its
reduced closure maps properly to the reduced closure of its base image.
The finite branch correction below is chosen before any horizontal cover
is quantified. The exceptional divisors `E_j` in `paper-p.tex`,
Theorem `thm:tower-restrict`, are instances of the fixed point `dY`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
-- This specialization synthesizes finite-type and normalization instances for a Rees component.
/-- One finite set for every finite cover above a chosen component of the
actual normalized Rees blow-up of a fixed affine target centre. -/
theorem exists_finite_bad_for_fixed_normalizedRees_component
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {R : Type u} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (dY : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      SchemeDivisorPoint (Palomar.normalization (reesProj I)))) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let β := normalizedReesProjToSpec I a ha
    let Y₀ := (pointClosureIdealSheaf dY.1).subscheme
    let Z₀ := (pointClosureIdealSheaf (β dY.1)).subscheme
    let q := pointClosureSubschemeMap β dY.1 (β dY.1) rfl
    let sR : Spec (.of R) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k R))
    letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
    letI : IsLocallyNoetherian Z₀ := inferInstance
    letI : LocallyOfFiniteType ((pointClosureIdealSheaf (β dY.1)).subschemeι ≫ sR) := by
      letI : LocallyOfFiniteType sR := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.finiteType_algebraMap.mpr inferInstance
      infer_instance
    letI : IsFinite (Palomar.normalizationMap Z₀) :=
      schemeGlobalNormalizationMap_isFinite Z₀ k
        ((pointClosureIdealSheaf (β dY.1)).subschemeι ≫ sR)
    ∃ Bad : Set Z₀, Bad.Finite ∧
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
        (_hmono : IsPrimeToPMonodromyMap p g)
        (D : SchemeDivisorPoint Z₀),
        D.1 ∉ Bad →
        (∀ E : SchemeDivisorPoint X,
          q (F E.1) = D.1 → (F.stalkMap E.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet g := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  let Y₀ := (pointClosureIdealSheaf dY.1).subscheme
  let Z₀ := (pointClosureIdealSheaf (β dY.1)).subscheme
  let q := pointClosureSubschemeMap β dY.1 (β dY.1) rfl
  let sR : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : NoetherianSpace (Spec (.of R)) := inferInstance
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper β := by dsimp only [β, normalizedReesProjToSpec]; infer_instance
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
    reesProjToSpecField_locallyOfFiniteType k I hI
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpecField (k := k) I)
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj I)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap (reesProj I))
  letI : NoetherianSpace (Palomar.normalization (reesProj I)) :=
    normalizedReesProj_noetherianSpace k I hI a ha
  letI : IsLocallyNoetherian Y₀ := inferInstance
  letI : NoetherianSpace Y₀ := inferInstance
  letI : IsLocallyNoetherian Z₀ := inferInstance
  letI : NoetherianSpace Z₀ := inferInstance
  letI : IsDominant q := pointClosureSubschemeMap_isDominant β dY.1 (β dY.1) rfl
  letI : IsProper q := pointClosureSubschemeMap_isProper β dY.1 (β dY.1) rfl
  let sY : Y₀ ⟶ Spec (.of k) :=
    (pointClosureIdealSheaf dY.1).subschemeι ≫ β ≫ sR
  let sZ : Z₀ ⟶ Spec (.of k) :=
    (pointClosureIdealSheaf (β dY.1)).subschemeι ≫ sR
  letI : LocallyOfFiniteType sY := inferInstance
  letI : LocallyOfFiniteType sZ := inferInstance
  letI : IsFinite (Palomar.normalizationMap Y₀) :=
    schemeGlobalNormalizationMap_isFinite Y₀ k sY
  letI : IsFinite (Palomar.normalizationMap Z₀) :=
    schemeGlobalNormalizationMap_isFinite Z₀ k sZ
  letI : NoetherianSpace (Palomar.normalization Z₀) := inferInstance
  let sZn : Palomar.normalization Z₀ ⟶ Spec (.of k) :=
    Palomar.normalizationMap Z₀ ≫ sZ
  exact exists_finite_bad_for_original_component_map p k sY sZn q

#print axioms exists_finite_bad_for_fixed_normalizedRees_component

end
end Pcf.Bounding.AllCodimBlowup
