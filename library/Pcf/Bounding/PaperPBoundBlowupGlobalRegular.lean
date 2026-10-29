/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundBlowupGlobalValuation
public import Pcf.Bounding.PaperPBlowupNonNormalCorrection
public import Pcf.Bounding.AllCodimCoreGood
public import Pcf.Stacks.Purity.DimensionOne

/-!
# Regularity at divisors outside the excluded set of `prop:bound-blowup`

`latex/paper-p.tex`, proof of Proposition `prop:bound-blowup`: the excluded finite set contains
the divisors of `B` inside `Sing B` and those dominated by a divisor of `B'` inside `Sing B'`.
Outside it, "As `B` is regular at the generic point of `D`" and "`B'` is regular" at every divisor
`F` of `B'` over `D` are the inputs of the valuation display.

At a codimension-one point of a Noetherian integral scheme, regular, normal and DVR stalks are the
same condition, so the excluded set here consists of the non-normal divisors of `B` and the
`q`-images of the non-normal divisors of `B'`. Both are finite
(`finite_nonNormal_component_divisor_image`, the `lem:finitely-many` input). The codimension
bookkeeping `F = f'(ν F'')` and `D = q(F)` is proved, and the display then holds with no
regularity hypothesis.

* `exists_finite_nonregular_bad`: the regularity part of the excluded set.
* `exists_finite_regular_bad_for_global_blowup_component` (and `_charZero`): the uniform bound of
  `exists_finite_bad_for_global_blowup_component` with the regularity clauses added.
* `BlowupRestrictionData.exists_finite_bad_valuation_display`: the display of `prop:bound-blowup`
  for every `F''` with `q(f'(ν F''))` outside one finite set.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

/-- A normal codimension-one stalk of a locally Noetherian integral scheme is a discrete valuation
ring (Stacks 00PD, normal-local half). -/
theorem stalk_isDiscreteValuationRing_of_coheight_eq_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (x : X) (hx : Order.coheight x = 1)
    (h : IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  haveI := h
  refine Pcf.Stacks.isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one _ ?_
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hx]
  rfl

variable {Y : Scheme.{u}} [IsIntegral Y] [CompactSpace Y]

/-- The regularity part of the excluded set of `prop:bound-blowup`: one finite set of points of
`B = closure {b}`, depending only on `Y`, `b` and the generic point `y'` of `B'`, outside of which
`B` is regular at every divisor and `B'` is regular at every divisor over it. -/
theorem exists_finite_nonregular_bad (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (b : Y) [Fact (genericPoint Y ∉ (pointCentre b).support)]
    (y' : globalNormalizedBlowup (pointCentre b))
    (hy' : globalNormalizedBlowupToBase (pointCentre b) y' = b) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsLocallyNoetherian (globalNormalizedBlowup (pointCentre b)) :=
      letI := globalNormalizedBlowup_locallyOfFiniteType_over (pointCentre b) k s
      LocallyOfFiniteType.isLocallyNoetherian (globalNormalizedBlowupToBase (pointCentre b) ≫ s)
    ∃ Bad : Set (pointClosureIdealSheaf b).subscheme, Bad.Finite ∧
      (∀ E : SchemeDivisorPoint (pointClosureIdealSheaf b).subscheme, E.1 ∉ Bad →
        IsDiscreteValuationRing ((pointClosureIdealSheaf b).subscheme.presheaf.stalk E.1)) ∧
      (∀ F : SchemeDivisorPoint (pointClosureIdealSheaf y').subscheme,
        pointClosureSubschemeMap (globalNormalizedBlowupToBase (pointCentre b)) y' b hy' F.1 ∉
          Bad →
        IsDiscreteValuationRing ((pointClosureIdealSheaf y').subscheme.presheaf.stalk F.1)) := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  let β := globalNormalizedBlowupToBase (pointCentre b)
  haveI : LocallyOfFiniteType (β ≫ s) := globalNormalizedBlowup_locallyOfFiniteType_over _ k s
  haveI : IsNoetherian (globalNormalizedBlowup (pointCentre b)) :=
    globalNormalizedBlowup_isNoetherian _ k s
  haveI : IsNoetherian Y := {}
  let Y₀ := (pointClosureIdealSheaf y').subscheme
  let Z₀ := (pointClosureIdealSheaf b).subscheme
  let q := pointClosureSubschemeMap β y' b hy'
  let sY : Y₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf y').subschemeι ≫ β ≫ s
  let sZ : Z₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf b).subschemeι ≫ s
  haveI : LocallyOfFiniteType sY := by dsimp only [sY]; infer_instance
  haveI : LocallyOfFiniteType sZ := by dsimp only [sZ]; infer_instance
  let NB := (fun d : SchemeDivisorPoint Z₀ => (𝟙 Z₀ : Z₀ ⟶ Z₀) d.1) ''
    {d | ¬ IsIntegrallyClosed (Z₀.presheaf.stalk d.1)}
  let NB' := (fun d : SchemeDivisorPoint Y₀ => q d.1) ''
    {d | ¬ IsIntegrallyClosed (Y₀.presheaf.stalk d.1)}
  refine ⟨NB ∪ NB', (finite_nonNormal_component_divisor_image k sZ (𝟙 Z₀)).union
    (finite_nonNormal_component_divisor_image k sY q), ?_, ?_⟩
  · intro E hE
    refine stalk_isDiscreteValuationRing_of_coheight_eq_one E.1 E.2 ?_
    by_contra hnn
    exact hE (Or.inl ⟨E, hnn, rfl⟩)
  · intro F hF
    refine stalk_isDiscreteValuationRing_of_coheight_eq_one F.1 F.2 ?_
    by_contra hnn
    exact hF (Or.inr ⟨F, hnn, rfl⟩)

variable [IsNormalScheme Y]

/-- **`prop:bound-blowup`, global form with its full excluded set, characteristic `p`.** One
finite set `Bad`, chosen from `Y`, `b` and `y'` only: outside it `B` and `B'` are regular at the
relevant divisors, and étaleness of `f'|_{A'}` excludes `branch(g)` for every compatible cover. -/
theorem exists_finite_regular_bad_for_global_blowup_component
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (b : Y) [Fact (genericPoint Y ∉ (pointCentre b).support)]
    (y' : globalNormalizedBlowup (pointCentre b))
    (hy' : globalNormalizedBlowupToBase (pointCentre b) y' = b) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsLocallyNoetherian (globalNormalizedBlowup (pointCentre b)) :=
      letI := globalNormalizedBlowup_locallyOfFiniteType_over (pointCentre b) k s
      LocallyOfFiniteType.isLocallyNoetherian (globalNormalizedBlowupToBase (pointCentre b) ≫ s)
    letI : IsFinite (Palomar.normalizationMap (pointClosureIdealSheaf b).subscheme) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k ((pointClosureIdealSheaf b).subschemeι ≫ s)
    ∃ Bad : Set (pointClosureIdealSheaf b).subscheme, Bad.Finite ∧
      (∀ E : SchemeDivisorPoint (pointClosureIdealSheaf b).subscheme, E.1 ∉ Bad →
        IsDiscreteValuationRing ((pointClosureIdealSheaf b).subscheme.presheaf.stalk E.1)) ∧
      (∀ F : SchemeDivisorPoint (pointClosureIdealSheaf y').subscheme,
        pointClosureSubschemeMap (globalNormalizedBlowupToBase (pointCentre b)) y' b hy' F.1 ∉
          Bad →
        IsDiscreteValuationRing ((pointClosureIdealSheaf y').subscheme.presheaf.stalk F.1)) ∧
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
  obtain ⟨Bad₀, hBad₀, h₀⟩ := exists_finite_bad_for_global_blowup_component p k s b y' hy'
  obtain ⟨Bad₁, hBad₁, hB, hB'⟩ := exists_finite_nonregular_bad k s b y' hy'
  refine ⟨Bad₀ ∪ Bad₁, hBad₀.union hBad₁, fun E hE ↦ hB E (fun h ↦ hE (Or.inr h)),
    fun F hF ↦ hB' F (fun h ↦ hF (Or.inr h)), ?_⟩
  intro X _ f _ _ hmono a D hD _ _ E hE heta
  exact h₀ f hmono D hD E (fun h ↦ hE (Or.inl h)) heta

omit [IsNormalScheme Y] in
/-- **`prop:bound-blowup`, global form with its full excluded set, characteristic zero.** -/
theorem exists_finite_regular_bad_for_global_blowup_component_charZero
    (k : Type u) [Field k] [CharZero k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (b : Y) [Fact (genericPoint Y ∉ (pointCentre b).support)]
    (y' : globalNormalizedBlowup (pointCentre b))
    (hy' : globalNormalizedBlowupToBase (pointCentre b) y' = b) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsLocallyNoetherian (globalNormalizedBlowup (pointCentre b)) :=
      letI := globalNormalizedBlowup_locallyOfFiniteType_over (pointCentre b) k s
      LocallyOfFiniteType.isLocallyNoetherian (globalNormalizedBlowupToBase (pointCentre b) ≫ s)
    letI : IsFinite (Palomar.normalizationMap (pointClosureIdealSheaf b).subscheme) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k ((pointClosureIdealSheaf b).subschemeι ≫ s)
    ∃ Bad : Set (pointClosureIdealSheaf b).subscheme, Bad.Finite ∧
      (∀ E : SchemeDivisorPoint (pointClosureIdealSheaf b).subscheme, E.1 ∉ Bad →
        IsDiscreteValuationRing ((pointClosureIdealSheaf b).subscheme.presheaf.stalk E.1)) ∧
      (∀ F : SchemeDivisorPoint (pointClosureIdealSheaf y').subscheme,
        pointClosureSubschemeMap (globalNormalizedBlowupToBase (pointCentre b)) y' b hy' F.1 ∉
          Bad →
        IsDiscreteValuationRing ((pointClosureIdealSheaf y').subscheme.presheaf.stalk F.1)) ∧
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
  obtain ⟨Bad₀, hBad₀, h₀⟩ := exists_finite_bad_for_global_blowup_component_charZero k s b y' hy'
  obtain ⟨Bad₁, hBad₁, hB, hB'⟩ := exists_finite_nonregular_bad k s b y' hy'
  refine ⟨Bad₀ ∪ Bad₁, hBad₀.union hBad₁, fun E hE ↦ hB E (fun h ↦ hE (Or.inr h)),
    fun F hF ↦ hB' F (fun h ↦ hF (Or.inr h)), ?_⟩
  intro X _ f _ _ a D hD _ _ E hE heta
  exact h₀ f D hD E (fun h ↦ hE (Or.inl h)) heta

set_option maxHeartbeats 1600000 in
-- The statement synthesizes Noetherian, finiteness and DVR instances on four normalizations.
omit [IsNormalScheme Y] in
/-- **The display of `prop:bound-blowup` outside the excluded set.** There is a finite set of
points of `B`, depending only on `Y`, `b` and `B'`, such that for every divisor `F''` of `Ã'` over
a divisor `D₁ = α̃(F'')` of `Ã` with `D = q(f'(ν F''))` outside it, and `f'|_{A'}` étale at
`F' = ν F''`: `B'` is regular at `F = f'(F')`, `B` is regular at `D`, and for uniformizers `t` of
`𝒪_{B,D}` and `t₁` of `𝒪_{Ã,D₁}`,
`v_F(q^* t) = v_{F''}(α̃^* g̃^* t) = e(D₁/D̃) · v_{F''}(α̃^* t₁)`. -/
theorem BlowupRestrictionData.exists_finite_bad_valuation_display (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Y} [IsFinite f] [IsDominant f] {a : X} {b : Y}
    [Fact (genericPoint Y ∉ (pointCentre b).support)] (D : BlowupRestrictionData f a b) :
    ∃ Bad : Set D.B, Bad.Finite ∧
      ∀ (x : SchemeDivisorPoint (Palomar.normalization D.A'))
        (hD₁ : Order.coheight (D.αTilde x.1) = 1),
        D.q (D.liftRestrict (D.ν x.1)) ∉ Bad →
        (D.liftRestrict.stalkMap (D.ν x.1)).hom.FormallyEtale →
        ∀ (t : D.B.presheaf.stalk (D.q (D.liftRestrict (D.ν x.1)))), Irreducible t →
        ∀ {t₁ : (Palomar.normalization D.A).presheaf.stalk (D.αTilde x.1)}, Irreducible t₁ →
        ∃ (h₁ : IsDiscreteValuationRing (D.B'.presheaf.stalk (D.liftRestrict (D.ν x.1))))
          (h₂ : IsDiscreteValuationRing (D.B.presheaf.stalk (D.q (D.liftRestrict (D.ν x.1))))),
        letI := h₁
        letI := h₂
        letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
        letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
        letI : LocallyOfFiniteType (BlowupRestrictionData.α f b ≫ f ≫ s) :=
          globalNormalizedBlowup_locallyOfFiniteType_over _ k (f ≫ s)
        letI : IsLocallyNoetherian (globalNormalizedBlowup ((pointCentre b).comap f)) :=
          LocallyOfFiniteType.isLocallyNoetherian (BlowupRestrictionData.α f b ≫ f ≫ s)
        letI : IsFinite (Palomar.normalizationMap D.A') :=
          Pcf.schemeGlobalNormalizationMap_isFinite _ k
            ((pointClosureIdealSheaf D.point).subschemeι ≫ BlowupRestrictionData.α f b ≫ f ≫ s)
        letI : IsFinite (Palomar.normalizationMap D.A) :=
          Pcf.schemeGlobalNormalizationMap_isFinite _ k
            ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
        letI : IsFinite (Palomar.normalizationMap D.B) :=
          Pcf.schemeGlobalNormalizationMap_isFinite _ k
            ((pointClosureIdealSheaf b).subschemeι ≫ s)
        letI : IsLocallyNoetherian (Palomar.normalization D.A') :=
          LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.A')
        letI : IsLocallyNoetherian (Palomar.normalization D.A) :=
          LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.A)
        letI : IsLocallyNoetherian (Palomar.normalization D.B) :=
          LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.B)
        let D₁ : SchemeDivisorPoint (Palomar.normalization D.A) := ⟨D.αTilde x.1, hD₁⟩
        letI : IsDiscreteValuationRing ((Palomar.normalization D.A').presheaf.stalk x.1) :=
          x.stalk_isDiscreteValuationRing
        letI : IsDiscreteValuationRing
            ((Palomar.normalization D.A).presheaf.stalk (D.αTilde x.1)) :=
          D₁.stalk_isDiscreteValuationRing
        letI : IsDiscreteValuationRing
            ((Palomar.normalization D.B).presheaf.stalk (D.gTilde (D.αTilde x.1))) :=
          (D₁.mapFiniteDominantNormal D.gTilde).stalk_isDiscreteValuationRing
        letI := (D.gTilde.stalkMap (D.αTilde x.1)).hom.toAlgebra
        let tt := (D.B.presheaf.stalkCongr
          (.of_eq (congrArg (fun φ ↦ φ x.1) D.normalized_square))).hom t
        addVal (D.B'.presheaf.stalk (D.liftRestrict (D.ν x.1)))
            (D.q.stalkMap (D.liftRestrict (D.ν x.1)) t) =
          addVal ((Palomar.normalization D.A').presheaf.stalk x.1)
            (D.αTilde.stalkMap x.1 ((D.gTilde ≫ D.νB).stalkMap (D.αTilde x.1) tt)) ∧
        addVal ((Palomar.normalization D.A').presheaf.stalk x.1)
            (D.αTilde.stalkMap x.1 ((D.gTilde ≫ D.νB).stalkMap (D.αTilde x.1) tt)) =
          ((maximalIdeal ((Palomar.normalization D.A).presheaf.stalk
              (D.αTilde x.1))).ramificationIdx
              ((Palomar.normalization D.B).presheaf.stalk (D.gTilde (D.αTilde x.1))) : ℕ∞) *
            addVal ((Palomar.normalization D.A').presheaf.stalk x.1)
              (D.αTilde.stalkMap x.1 t₁) := by
  obtain ⟨Bad, hBad, hB, hB'⟩ := exists_finite_nonregular_bad k s b D.imagePoint D.β_imagePoint
  refine ⟨Bad, hBad, ?_⟩
  intro x hD₁ hnot hetale t ht t₁ ht₁
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
  haveI : LocallyOfFiniteType (BlowupRestrictionData.α f b ≫ f ≫ s) :=
    globalNormalizedBlowup_locallyOfFiniteType_over _ k (f ≫ s)
  haveI : IsLocallyNoetherian (globalNormalizedBlowup ((pointCentre b).comap f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (BlowupRestrictionData.α f b ≫ f ≫ s)
  haveI : LocallyOfFiniteType (BlowupRestrictionData.β b ≫ s) :=
    globalNormalizedBlowup_locallyOfFiniteType_over _ k s
  haveI : IsLocallyNoetherian (globalNormalizedBlowup (pointCentre b)) :=
    LocallyOfFiniteType.isLocallyNoetherian (BlowupRestrictionData.β b ≫ s)
  let sA' : D.A' ⟶ Spec (.of k) :=
    (pointClosureIdealSheaf D.point).subschemeι ≫ BlowupRestrictionData.α f b ≫ f ≫ s
  let sB' : D.B' ⟶ Spec (.of k) :=
    (pointClosureIdealSheaf D.imagePoint).subschemeι ≫ BlowupRestrictionData.β b ≫ s
  let sB : D.B ⟶ Spec (.of k) := (pointClosureIdealSheaf b).subschemeι ≫ s
  haveI : LocallyOfFiniteType sA' := by dsimp only [sA']; infer_instance
  haveI : LocallyOfFiniteType sB' := by dsimp only [sB']; infer_instance
  haveI : LocallyOfFiniteType sB := by dsimp only [sB]; infer_instance
  haveI : IsFinite (Palomar.normalizationMap D.A') :=
    Pcf.schemeGlobalNormalizationMap_isFinite _ k sA'
  haveI : IsFinite (Palomar.normalizationMap D.A) := Pcf.schemeGlobalNormalizationMap_isFinite _ k
    ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
  haveI : IsFinite (Palomar.normalizationMap D.B) :=
    Pcf.schemeGlobalNormalizationMap_isFinite _ k sB
  haveI : IsLocallyNoetherian (Palomar.normalization D.A) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.A)
  haveI : IsLocallyNoetherian (Palomar.normalization D.B) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.B)
  haveI := globalNormalizedBlowupMap_isFinite f (pointCentre b) k s
  haveI : IsFinite D.liftRestrict := pointClosureSubschemeMap_isFinite _ _ _ _
  -- Codimension bookkeeping: `F' = ν F''`, `F = f'(F')` and `D = q(F)` are divisors.
  let F' : SchemeDivisorPoint D.A' := normalizationMap_divisorPoint k sA' x
  have hF : Order.coheight (D.liftRestrict (D.ν x.1)) = 1 :=
    coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sB' D.liftRestrict F'
  let D₁ : SchemeDivisorPoint (Palomar.normalization D.A) := ⟨D.αTilde x.1, hD₁⟩
  haveI : IsFinite D.gTilde := inferInstance
  let Dt : SchemeDivisorPoint (Palomar.normalization D.B) := D₁.mapFiniteDominantNormal D.gTilde
  have hpt : D.q (D.liftRestrict (D.ν x.1)) = D.νB (D.gTilde (D.αTilde x.1)) := by
    have h := congrArg (fun φ ↦ φ x.1) D.normalized_square
    simpa only [Scheme.Hom.comp_apply] using h
  have hD : Order.coheight (D.q (D.liftRestrict (D.ν x.1))) = 1 := by
    rw [hpt]
    exact coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sB D.νB Dt
  have h₁ := hB' ⟨_, hF⟩ hnot
  have h₂ := hB ⟨_, hD⟩ hnot
  exact ⟨h₁, h₂, D.boundBlowup_valuation_display k s x hD₁ hetale t ht ht₁⟩

#print axioms exists_finite_nonregular_bad
#print axioms exists_finite_regular_bad_for_global_blowup_component
#print axioms exists_finite_regular_bad_for_global_blowup_component_charZero
#print axioms BlowupRestrictionData.exists_finite_bad_valuation_display

end
end Pcf.Bounding.AllCodimBlowup
