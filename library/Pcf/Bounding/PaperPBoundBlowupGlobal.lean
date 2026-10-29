/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalRestrictionData
public import Pcf.Bounding.PaperPBlowupOriginalEtaleUniformCharZero
public import Pcf.Bounding.AllCentrePointClosureMonodromy

/-!
# `prop:bound-blowup` on the global normalized blow-up

`latex/paper-p.tex`, Proposition `prop:bound-blowup`: for blow-up restriction data
`(f, A, B, X', Y', α, β, f', g, A', B')` with `f` of monodromy not divisible by `p`, `B'` is an
irreducible component of `β⁻¹(B)` dominating `B`, and there is a finite set of integral effective
divisors of `B`, depending only on `Y`, `B` and `B'`, such that every other divisor `D` of `B`
over which `f'|_{A'}` is étale is not a component of `branch(g)`.

Here the data live on the actual global normalized blow-ups of
`AllCodimBlowupGlobalRestrictionData`. The finite set is chosen from `Y`, the centre point `b`
(the generic point of `B`) and the generic point `y'` of `B'` alone, before the finite cover
`f : X ⟶ Y`, the subvariety `A`, and the component `A'` are quantified. The proof applies the
scheme-level fixed-component theorem `exists_finite_bad_for_original_component_map` (and its
characteristic-zero form) directly to the proper map `q = β|_{B'} : B' ⟶ B` of reduced point
closures: no affine chart reduction is needed, because the global `β` is proper
(`globalNormalizedBlowupToBase_isProper`) and `Y'` is Noetherian.

Divisors are encoded as in the affine rows: `SchemeDivisorPoint` of the reduced closures, and
`branch(g)` is the normalized weighted branch set `weightedBranchPointSet g`. The étaleness
premise is the stalkwise one at every divisor of `A'` over `D`, as in
`exists_finite_bad_for_actual_affine_Rees_source_component`.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

variable {Y : Scheme.{u}}

/-- The restriction `g = f|_A : A ⟶ B` has monodromy not divisible by `p` when `f` does
(`lem:allcodim-monodromy`), for any name `b` of the image point. -/
theorem pointClosureMap_primeToPMonodromy_of_eq (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    [CharP k p] {X : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f) (a : X) (b : Y) (hab : f a = b) :
    letI : IsFinite (pointClosureSubschemeMap f a b hab) :=
      pointClosureSubschemeMap_isFinite _ _ _ _
    letI : IsDominant (pointClosureSubschemeMap f a b hab) :=
      pointClosureSubschemeMap_isDominant _ _ _ _
    IsPrimeToPMonodromyMap p (pointClosureSubschemeMap f a b hab) := by
  subst hab
  exact finiteType_pointClosureMap_primeToPMonodromy p (Fact.out) k f s hmono a

/-- Noetherian instances on the normalized blow-up of a Noetherian scheme of finite type over a
field. -/
theorem globalNormalizedBlowup_isNoetherian [IsIntegral Y] [CompactSpace Y]
    (I : Y.IdealSheafData) [Fact (genericPoint Y ∉ I.support)] (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] : IsNoetherian (globalNormalizedBlowup I) := by
  haveI := globalNormalizedBlowupToBase_isProper I k s
  haveI := globalNormalizedBlowup_locallyOfFiniteType_over I k s
  haveI : IsLocallyNoetherian (globalNormalizedBlowup I) :=
    LocallyOfFiniteType.isLocallyNoetherian (globalNormalizedBlowupToBase I ≫ s)
  haveI : CompactSpace (globalNormalizedBlowup I) :=
    QuasiCompact.compactSpace_of_compactSpace (globalNormalizedBlowupToBase I)
  exact {}

variable [IsIntegral Y] [IsNormalScheme Y] [CompactSpace Y]

set_option maxHeartbeats 1600000 in
-- Uniformity requires synthesizing finiteness and Noetherian instances for every varying cover.
/-- **`prop:bound-blowup`, global form, characteristic `p`.** Fix `Y` normal integral of finite
type over `k`, the generic point `b ≠ η_Y` of `B`, and the generic point `y'` of a component `B'`
of `β⁻¹(B)` dominating `B` on the actual normalized blow-up `Y'`. There is one finite set `Bad`
of points of `B` such that for *every* finite surjective `f : X ⟶ Y` of integral schemes with
monodromy not divisible by `p`, every `A = closure {a}` with `f(A) = B`, and every component
`A'` of `α⁻¹(A)` dominating `A` with `f'(A') = B'`: each divisor `D` of `B` outside `Bad` over
which `f'|_{A'}` is étale (at every divisor of `A'` over `D`) is not in `branch(g)`.

`paper-p.tex` correspondence: Proposition 7.11 (`prop:bound-blowup`). -/
theorem exists_finite_bad_for_global_blowup_component
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (b : Y) [Fact (genericPoint Y ∉ (pointCentre b).support)]
    (y' : globalNormalizedBlowup (pointCentre b))
    (hy' : globalNormalizedBlowupToBase (pointCentre b) y' = b) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsFinite (Palomar.normalizationMap (pointClosureIdealSheaf b).subscheme) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k ((pointClosureIdealSheaf b).subschemeι ≫ s)
    ∃ Bad : Set (pointClosureIdealSheaf b).subscheme, Bad.Finite ∧
      ∀ {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) [IsFinite f] [IsDominant f]
        (_hmono : IsPrimeToPMonodromyMap p f) {a : X} (D : BlowupRestrictionData f a b)
        (hD : BlowupRestrictionData.lift f b D.point = y'),
        letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
        letI : IsFinite (Palomar.normalizationMap D.A) :=
          Pcf.schemeGlobalNormalizationMap_isFinite _ k
            ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
        let u := pointClosureSubschemeMap (BlowupRestrictionData.lift f b) D.point y' hD
        let q := pointClosureSubschemeMap (BlowupRestrictionData.β b) y' b hy'
        ∀ E : SchemeDivisorPoint (pointClosureIdealSheaf b).subscheme, E.1 ∉ Bad →
          (∀ F : SchemeDivisorPoint D.A', q (u F.1) = E.1 → (u.stalkMap F.1).hom.FormallyEtale) →
          E.1 ∉ weightedBranchPointSet D.g := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  let β := globalNormalizedBlowupToBase (pointCentre b)
  haveI : IsProper β := globalNormalizedBlowupToBase_isProper _ k s
  haveI : LocallyOfFiniteType (β ≫ s) := globalNormalizedBlowup_locallyOfFiniteType_over _ k s
  haveI : IsNoetherian (globalNormalizedBlowup (pointCentre b)) :=
    globalNormalizedBlowup_isNoetherian _ k s
  haveI : IsNoetherian Y := {}
  let Y₀ := (pointClosureIdealSheaf y').subscheme
  let Z₀ := (pointClosureIdealSheaf b).subscheme
  let q := pointClosureSubschemeMap β y' b hy'
  haveI : IsProper q := pointClosureSubschemeMap_isProper β y' b hy'
  haveI : IsDominant q := pointClosureSubschemeMap_isDominant β y' b hy'
  let sY : Y₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf y').subschemeι ≫ β ≫ s
  let sZ : Z₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf b).subschemeι ≫ s
  haveI : LocallyOfFiniteType sY := by dsimp only [sY]; infer_instance
  haveI : LocallyOfFiniteType sZ := by dsimp only [sZ]; infer_instance
  haveI : IsFinite (Palomar.normalizationMap Y₀) :=
    Pcf.schemeGlobalNormalizationMap_isFinite Y₀ k sY
  haveI : IsFinite (Palomar.normalizationMap Z₀) :=
    Pcf.schemeGlobalNormalizationMap_isFinite Z₀ k sZ
  haveI : NoetherianSpace (Palomar.normalization Z₀) := inferInstance
  obtain ⟨Bad, hBad, hbound⟩ :=
    Pcf.Bounding.exists_finite_bad_for_original_component_map p k sY
      (Palomar.normalizationMap Z₀ ≫ sZ) q
  refine ⟨Bad, hBad, ?_⟩
  intro X _ f _ _ hmono a D hD
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
  let α := globalNormalizedBlowupToBase ((pointCentre b).comap f)
  haveI : IsProper α := globalNormalizedBlowupToBase_isProper _ k (f ≫ s)
  haveI : LocallyOfFiniteType (α ≫ f ≫ s) :=
    globalNormalizedBlowup_locallyOfFiniteType_over _ k (f ≫ s)
  haveI : IsLocallyNoetherian (globalNormalizedBlowup ((pointCentre b).comap f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (α ≫ f ≫ s)
  haveI := globalNormalizedBlowupMap_isFinite f (pointCentre b) k s
  let X₀ := (pointClosureIdealSheaf D.point).subscheme
  let W₀ := (pointClosureIdealSheaf a).subscheme
  let sX : X₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf D.point).subschemeι ≫ α ≫ f ≫ s
  haveI : LocallyOfFiniteType sX := by dsimp only [sX]; infer_instance
  haveI : IsFinite (Palomar.normalizationMap X₀) :=
    Pcf.schemeGlobalNormalizationMap_isFinite X₀ k sX
  haveI : IsFinite (Palomar.normalizationMap W₀) := Pcf.schemeGlobalNormalizationMap_isFinite _ k
    ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
  let u := pointClosureSubschemeMap (BlowupRestrictionData.lift f b) D.point y' hD
  haveI : IsFinite u := pointClosureSubschemeMap_isFinite _ _ _ _
  haveI : IsDominant u := pointClosureSubschemeMap_isDominant _ _ _ _
  let v := pointClosureSubschemeMap α D.point a D.dominates
  haveI : IsProper v := pointClosureSubschemeMap_isProper _ _ _ _
  haveI : IsDominant v := pointClosureSubschemeMap_isDominant _ _ _ _
  have hsq : u ≫ q = v ≫ D.g := by
    apply (cancel_mono (pointClosureIdealSheaf b).subschemeι).mp
    simp only [u, q, v, Category.assoc, pointClosureSubschemeMap_subschemeι,
      pointClosureSubschemeMap_subschemeι_assoc]
    exact congrArg ((pointClosureIdealSheaf D.point).subschemeι ≫ ·)
      (globalNormalizedBlowupMap_comm f (pointCentre b))
  have hmonog := pointClosureMap_primeToPMonodromy_of_eq p k s f hmono a b D.map_centre
  intro _ _ E hE heta
  exact hbound sX u v D.g hsq hmonog E hE heta

set_option maxHeartbeats 1600000 in
-- Uniformity requires synthesizing finiteness and Noetherian instances for every varying cover.
omit [IsNormalScheme Y] in
/-- **`prop:bound-blowup`, global form, characteristic zero.** As
`exists_finite_bad_for_global_blowup_component`, with no monodromy hypothesis: in characteristic
zero every finite cover has monodromy not divisible by the characteristic. Normality of `Y` is
not needed here.

`paper-p.tex` correspondence: Proposition 7.11 (`prop:bound-blowup`). -/
theorem exists_finite_bad_for_global_blowup_component_charZero
    (k : Type u) [Field k] [CharZero k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (b : Y) [Fact (genericPoint Y ∉ (pointCentre b).support)]
    (y' : globalNormalizedBlowup (pointCentre b))
    (hy' : globalNormalizedBlowupToBase (pointCentre b) y' = b) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsFinite (Palomar.normalizationMap (pointClosureIdealSheaf b).subscheme) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k ((pointClosureIdealSheaf b).subschemeι ≫ s)
    ∃ Bad : Set (pointClosureIdealSheaf b).subscheme, Bad.Finite ∧
      ∀ {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) [IsFinite f] [IsDominant f] {a : X}
        (D : BlowupRestrictionData f a b)
        (hD : BlowupRestrictionData.lift f b D.point = y'),
        letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
        letI : IsFinite (Palomar.normalizationMap D.A) :=
          Pcf.schemeGlobalNormalizationMap_isFinite _ k
            ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
        let u := pointClosureSubschemeMap (BlowupRestrictionData.lift f b) D.point y' hD
        let q := pointClosureSubschemeMap (BlowupRestrictionData.β b) y' b hy'
        ∀ E : SchemeDivisorPoint (pointClosureIdealSheaf b).subscheme, E.1 ∉ Bad →
          (∀ F : SchemeDivisorPoint D.A', q (u F.1) = E.1 → (u.stalkMap F.1).hom.FormallyEtale) →
          E.1 ∉ weightedBranchPointSet D.g := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  let β := globalNormalizedBlowupToBase (pointCentre b)
  haveI : IsProper β := globalNormalizedBlowupToBase_isProper _ k s
  haveI : LocallyOfFiniteType (β ≫ s) := globalNormalizedBlowup_locallyOfFiniteType_over _ k s
  haveI : IsNoetherian (globalNormalizedBlowup (pointCentre b)) :=
    globalNormalizedBlowup_isNoetherian _ k s
  haveI : IsNoetherian Y := {}
  let Y₀ := (pointClosureIdealSheaf y').subscheme
  let Z₀ := (pointClosureIdealSheaf b).subscheme
  let q := pointClosureSubschemeMap β y' b hy'
  haveI : IsProper q := pointClosureSubschemeMap_isProper β y' b hy'
  haveI : IsDominant q := pointClosureSubschemeMap_isDominant β y' b hy'
  let sY : Y₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf y').subschemeι ≫ β ≫ s
  let sZ : Z₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf b).subschemeι ≫ s
  haveI : LocallyOfFiniteType sY := by dsimp only [sY]; infer_instance
  haveI : LocallyOfFiniteType sZ := by dsimp only [sZ]; infer_instance
  haveI : IsFinite (Palomar.normalizationMap Y₀) :=
    Pcf.schemeGlobalNormalizationMap_isFinite Y₀ k sY
  haveI : IsFinite (Palomar.normalizationMap Z₀) :=
    Pcf.schemeGlobalNormalizationMap_isFinite Z₀ k sZ
  haveI : NoetherianSpace (Palomar.normalization Z₀) := inferInstance
  obtain ⟨Bad, hBad, hbound⟩ :=
    Pcf.Bounding.exists_finite_bad_for_original_component_map_charZero k sY
      (Palomar.normalizationMap Z₀ ≫ sZ) q
  refine ⟨Bad, hBad, ?_⟩
  intro X _ f _ _ a D hD
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
  let α := globalNormalizedBlowupToBase ((pointCentre b).comap f)
  haveI : IsProper α := globalNormalizedBlowupToBase_isProper _ k (f ≫ s)
  haveI : LocallyOfFiniteType (α ≫ f ≫ s) :=
    globalNormalizedBlowup_locallyOfFiniteType_over _ k (f ≫ s)
  haveI : IsLocallyNoetherian (globalNormalizedBlowup ((pointCentre b).comap f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (α ≫ f ≫ s)
  haveI := globalNormalizedBlowupMap_isFinite f (pointCentre b) k s
  let X₀ := (pointClosureIdealSheaf D.point).subscheme
  let W₀ := (pointClosureIdealSheaf a).subscheme
  let sX : X₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf D.point).subschemeι ≫ α ≫ f ≫ s
  haveI : LocallyOfFiniteType sX := by dsimp only [sX]; infer_instance
  haveI : IsFinite (Palomar.normalizationMap X₀) :=
    Pcf.schemeGlobalNormalizationMap_isFinite X₀ k sX
  haveI : IsFinite (Palomar.normalizationMap W₀) := Pcf.schemeGlobalNormalizationMap_isFinite _ k
    ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
  let u := pointClosureSubschemeMap (BlowupRestrictionData.lift f b) D.point y' hD
  haveI : IsFinite u := pointClosureSubschemeMap_isFinite _ _ _ _
  haveI : IsDominant u := pointClosureSubschemeMap_isDominant _ _ _ _
  let v := pointClosureSubschemeMap α D.point a D.dominates
  haveI : IsProper v := pointClosureSubschemeMap_isProper _ _ _ _
  haveI : IsDominant v := pointClosureSubschemeMap_isDominant _ _ _ _
  have hsq : u ≫ q = v ≫ D.g := by
    apply (cancel_mono (pointClosureIdealSheaf b).subschemeι).mp
    simp only [u, q, v, Category.assoc, pointClosureSubschemeMap_subschemeι,
      pointClosureSubschemeMap_subschemeι_assoc]
    exact congrArg ((pointClosureIdealSheaf D.point).subschemeι ≫ ·)
      (globalNormalizedBlowupMap_comm f (pointCentre b))
  intro _ _ E hE heta
  exact hbound sX u v D.g hsq E hE heta


/-- **`prop:bound-blowup` for fixed blow-up restriction data, characteristic `p`.** `B' = f'(A')`
is an irreducible component of `β⁻¹(B)` dominating `B`, and there is a finite set of divisors of
`B` outside of which étaleness of `f'|_{A'}` excludes `branch(g)`. The finite set depends only on
`Y`, `b` and the generic point of `B'`: see `exists_finite_bad_for_global_blowup_component` for the
uniform quantifier order.

`paper-p.tex` correspondence: Proposition 7.11 (`prop:bound-blowup`). -/
theorem BlowupRestrictionData.boundBlowup
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Y} [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f) {a : X} {b : Y}
    [Fact (genericPoint Y ∉ (pointCentre b).support)] (D : BlowupRestrictionData f a b) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsFinite (Palomar.normalizationMap D.B) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k ((pointClosureIdealSheaf b).subschemeι ≫ s)
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap D.A) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k
        ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
    (∀ h : D.imagePoint ∈ BlowupRestrictionData.β b ⁻¹' closure {b},
      closure {(⟨D.imagePoint, h⟩ : BlowupRestrictionData.β b ⁻¹' closure {b})} ∈
        irreducibleComponents (BlowupRestrictionData.β b ⁻¹' closure {b})) ∧
    BlowupRestrictionData.β b D.imagePoint = b ∧
    ∃ Bad : Set D.B, Bad.Finite ∧
      ∀ E : SchemeDivisorPoint D.B, E.1 ∉ Bad →
        (∀ F : SchemeDivisorPoint D.A', D.q (D.liftRestrict F.1) = E.1 →
          (D.liftRestrict.stalkMap F.1).hom.FormallyEtale) →
        E.1 ∉ weightedBranchPointSet D.g := by
  refine ⟨D.image_isComponent k s, D.β_imagePoint, ?_⟩
  obtain ⟨Bad, hBad, h⟩ :=
    exists_finite_bad_for_global_blowup_component p k s b D.imagePoint D.β_imagePoint
  exact ⟨Bad, hBad, fun E hE heta ↦ h f hmono D rfl E hE heta⟩

omit [IsNormalScheme Y] in
/-- **`prop:bound-blowup` for fixed blow-up restriction data, characteristic zero.**

`paper-p.tex` correspondence: Proposition 7.11 (`prop:bound-blowup`). -/
theorem BlowupRestrictionData.boundBlowup_charZero
    (k : Type u) [Field k] [CharZero k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Y} [IsFinite f] [IsDominant f] {a : X} {b : Y}
    [Fact (genericPoint Y ∉ (pointCentre b).support)] (D : BlowupRestrictionData f a b) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsFinite (Palomar.normalizationMap D.B) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k ((pointClosureIdealSheaf b).subschemeι ≫ s)
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap D.A) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k
        ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
    (∀ h : D.imagePoint ∈ BlowupRestrictionData.β b ⁻¹' closure {b},
      closure {(⟨D.imagePoint, h⟩ : BlowupRestrictionData.β b ⁻¹' closure {b})} ∈
        irreducibleComponents (BlowupRestrictionData.β b ⁻¹' closure {b})) ∧
    BlowupRestrictionData.β b D.imagePoint = b ∧
    ∃ Bad : Set D.B, Bad.Finite ∧
      ∀ E : SchemeDivisorPoint D.B, E.1 ∉ Bad →
        (∀ F : SchemeDivisorPoint D.A', D.q (D.liftRestrict F.1) = E.1 →
          (D.liftRestrict.stalkMap F.1).hom.FormallyEtale) →
        E.1 ∉ weightedBranchPointSet D.g := by
  refine ⟨D.image_isComponent k s, D.β_imagePoint, ?_⟩
  obtain ⟨Bad, hBad, h⟩ :=
    exists_finite_bad_for_global_blowup_component_charZero k s b D.imagePoint D.β_imagePoint
  exact ⟨Bad, hBad, fun E hE heta ↦ h f D rfl E hE heta⟩

#print axioms exists_finite_bad_for_global_blowup_component
#print axioms exists_finite_bad_for_global_blowup_component_charZero
#print axioms BlowupRestrictionData.boundBlowup
#print axioms BlowupRestrictionData.boundBlowup_charZero

end
end Pcf.Bounding.AllCodimBlowup
