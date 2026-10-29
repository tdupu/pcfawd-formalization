/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupNormalizedUniformBranch
public import Pcf.Bounding.PaperPBlowupComponentSquare
public import Pcf.Bounding.GlobalNormalizationFinite
public import Pcf.Bounding.AllCentrePointClosureMonodromy
public import Pcf.Bounding.AllCodimBlowupMonodromyTransport

/-!
# Uniform branch bound for an actual point-closure square

The four schemes here are the reduced closures of points in a proper square
of finite covers. The finite bad set depends on the fixed point-closure map
of the target vertical arrow. This removes the finite-normalization and
Noetherian assumptions from the abstract normalized-component theorem.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
-- The instance synthesis for all four point-closure normalizations needs extra heartbeats.
/-- The normalized point-closure square has a finite bad set selected by
the fixed proper target component map. -/
theorem exists_finite_bad_for_pointClosure_square
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {X Y X' Y' : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [NoetherianSpace Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (F : X' ⟶ Y')
    (α : X' ⟶ X) (β : Y' ⟶ Y)
    [IsFinite f] [IsDominant f] [IsFinite F] [IsProper α] [IsProper β]
    (hsquare : F ≫ β = α ≫ f) (x : X')
    (hmono : IsPrimeToPMonodromyMap p f) :
    let b := β (F x)
    let Z := (pointClosureIdealSheaf b).subscheme
    let q := pointClosureSubschemeMap β (F x) b rfl
    letI : IsDominant q := pointClosureSubschemeMap_isDominant _ _ _ _
    letI : IsProper q := AllCodimBlowup.pointClosureSubschemeMap_isProper _ _ _ _
    let u₀ := pointClosureSubschemeMap F x (F x) rfl
    letI : IsDominant u₀ := pointClosureSubschemeMap_isDominant _ _ _ _
    let hab : f (α x) = b := by
      have h := congrArg (fun m : X' ⟶ Y => m x) hsquare
      simpa only [Scheme.Hom.comp_apply] using h.symm
    let g₀ := pointClosureSubschemeMap f (α x) b hab
    letI : IsDominant g₀ := pointClosureSubschemeMap_isDominant _ _ _ _
    letI : IsFinite (Palomar.normalizationMap (pointClosureIdealSheaf x).subscheme) := by
      letI : LocallyOfFiniteType
          ((pointClosureIdealSheaf x).subschemeι ≫ α ≫ sX) := inferInstance
      exact schemeGlobalNormalizationMap_isFinite _ k
        ((pointClosureIdealSheaf x).subschemeι ≫ α ≫ sX)
    letI : IsFinite (Palomar.normalizationMap
        (pointClosureIdealSheaf (α x)).subscheme) := by
      letI : LocallyOfFiniteType
          ((pointClosureIdealSheaf (α x)).subschemeι ≫ sX) := inferInstance
      exact schemeGlobalNormalizationMap_isFinite _ k
        ((pointClosureIdealSheaf (α x)).subschemeι ≫ sX)
    letI : IsFinite (Palomar.normalizationMap Z) := by
      letI : LocallyOfFiniteType
          ((pointClosureIdealSheaf b).subschemeι ≫ sY) := inferInstance
      exact schemeGlobalNormalizationMap_isFinite _ k
        ((pointClosureIdealSheaf b).subschemeι ≫ sY)
    letI : IsFinite u₀ := pointClosureSubschemeMap_isFinite _ _ _ _
    letI : IsFinite g₀ := pointClosureSubschemeMap_isFinite _ _ _ _
    letI : IsFinite (Palomar.normalizationMap
        (Palomar.normalization (pointClosureIdealSheaf (α x)).subscheme)) := by
      letI : IsIso (Palomar.normalizationMap
          (Palomar.normalization (pointClosureIdealSheaf (α x)).subscheme)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Z)) := by
      letI : IsIso (Palomar.normalizationMap (Palomar.normalization Z)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    ∃ Bad : Set (Palomar.normalization Z), Bad.Finite ∧
      ∀ D : SchemeDivisorPoint (Palomar.normalization Z),
        D.1 ∉ Bad →
        (∀ e : SchemeDivisorPoint
          (Palomar.normalization (pointClosureIdealSheaf x).subscheme),
          (schemeDominantNormalizationMorphism q)
            ((schemeDominantNormalizationMorphism u₀) e.1) = D.1 →
          ((schemeDominantNormalizationMorphism u₀).stalkMap e.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet (schemeDominantNormalizationMorphism g₀) := by
  let a := α x
  let b := β (F x)
  have hab : f a = b := by
    have h := congrArg (fun m : X' ⟶ Y => m x) hsquare
    simpa only [Scheme.Hom.comp_apply] using h.symm
  let A' := (pointClosureIdealSheaf x).subscheme
  let B' := (pointClosureIdealSheaf (F x)).subscheme
  let A := (pointClosureIdealSheaf a).subscheme
  let B := (pointClosureIdealSheaf b).subscheme
  let u₀ := pointClosureSubschemeMap F x (F x) rfl
  let v₀ := pointClosureSubschemeMap α x a rfl
  let q₀ := pointClosureSubschemeMap β (F x) b rfl
  let g₀ := pointClosureSubschemeMap f a b hab
  letI : IsFinite u₀ := pointClosureSubschemeMap_isFinite _ _ _ _
  letI : IsFinite g₀ := pointClosureSubschemeMap_isFinite _ _ _ _
  letI : IsProper v₀ := AllCodimBlowup.pointClosureSubschemeMap_isProper _ _ _ _
  letI : IsProper q₀ := AllCodimBlowup.pointClosureSubschemeMap_isProper _ _ _ _
  letI : IsDominant u₀ := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsDominant v₀ := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsDominant q₀ := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsDominant g₀ := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : LocallyOfFiniteType (pointClosureIdealSheaf a).subschemeι := inferInstance
  letI : LocallyOfFiniteType (pointClosureIdealSheaf b).subschemeι := inferInstance
  letI : LocallyOfFiniteType (pointClosureIdealSheaf x).subschemeι := inferInstance
  letI : LocallyOfFiniteType (pointClosureIdealSheaf (F x)).subschemeι := inferInstance
  letI : LocallyOfFiniteType α := inferInstance
  letI : LocallyOfFiniteType β := inferInstance
  letI : LocallyOfFiniteType ((pointClosureIdealSheaf a).subschemeι ≫ sX) := inferInstance
  letI : LocallyOfFiniteType ((pointClosureIdealSheaf b).subschemeι ≫ sY) := inferInstance
  letI : LocallyOfFiniteType ((pointClosureIdealSheaf x).subschemeι ≫ α ≫ sX) := inferInstance
  letI : LocallyOfFiniteType ((pointClosureIdealSheaf (F x)).subschemeι ≫ β ≫ sY) := inferInstance
  letI : IsFinite (Palomar.normalizationMap A') :=
    schemeGlobalNormalizationMap_isFinite A' k
      ((pointClosureIdealSheaf x).subschemeι ≫ α ≫ sX)
  letI : IsFinite (Palomar.normalizationMap B') :=
    schemeGlobalNormalizationMap_isFinite B' k
      ((pointClosureIdealSheaf (F x)).subschemeι ≫ β ≫ sY)
  letI : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite A k
      ((pointClosureIdealSheaf a).subschemeι ≫ sX)
  letI : IsFinite (Palomar.normalizationMap B) :=
    schemeGlobalNormalizationMap_isFinite B k
      ((pointClosureIdealSheaf b).subschemeι ≫ sY)
  letI : NoetherianSpace B := pointClosureSubscheme_noetherian b
  letI : NoetherianSpace (Palomar.normalization B) := inferInstance
  have hsq : u₀ ≫ q₀ = v₀ ≫ g₀ :=
    AllCodimBlowup.pointClosureSubschemeMap_square f F α β hsquare x
  have hmono₀ : IsPrimeToPMonodromyMap p g₀ := by
    have hmono_for (y : Y) (hy : f a = y) :
        let t := pointClosureSubschemeMap f a y hy
        letI : IsFinite t := pointClosureSubschemeMap_isFinite _ _ _ _
        letI : IsDominant t := pointClosureSubschemeMap_isDominant _ _ _ _
        IsPrimeToPMonodromyMap p t := by
      subst y
      exact finiteType_pointClosureMap_primeToPMonodromy p (Fact.out) k f sY hmono a
    exact hmono_for b hab
  have hmonon : IsPrimeToPMonodromyMap p
      (schemeDominantNormalizationMorphism g₀) := by
    exact AllCodimBlowup.primeToPMonodromy_of_genericBirationalSquare
      p g₀ (schemeDominantNormalizationMorphism g₀)
      (Palomar.normalizationMap A) (Palomar.normalizationMap B)
      (schemeDominantNormalizationMorphism_comp_normalizationMap g₀) hmono₀
  simpa only [a, b, A', B', A, B, u₀, v₀, q₀, g₀] using
    exists_finite_bad_for_normalized_component_square
      p k ((Palomar.normalizationMap B) ≫
        (pointClosureIdealSheaf b).subschemeι ≫ sY)
      u₀ v₀ q₀ g₀ hsq hmonon

#print axioms exists_finite_bad_for_pointClosure_square

end
end Pcf.Bounding
