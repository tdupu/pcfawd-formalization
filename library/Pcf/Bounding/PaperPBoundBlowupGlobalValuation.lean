/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundBlowupGlobal
public import Pcf.Bounding.PaperPBoundBlowupValuationIdentity
public import Pcf.Bounding.PaperPBlowupEtaleNormalTransport
public import Pcf.Bounding.ClosureStalkNormalization
public import Pcf.Bounding.SchemeDynamics

/-!
# The valuation display of `prop:bound-blowup` on the actual `A'`, `B'`, `Ã'`

`latex/paper-p.tex`, proof of Proposition `prop:bound-blowup` ("Pushing down"), compares orders of
a local equation `t` of `D` around `q ∘ f'|_{A'} = g ∘ α|_{A'}`, lifted to `Ã'`:
`v_F(q^* t) = v_{F''}(α̃^* g̃^* t) = e · v_{F''}(α̃^* t₁)`.

`boundBlowup_valuation_identity_of_etale` proves this for an arbitrary square of schemes with
pointwise hypotheses. Here it is instantiated on the actual blow-up restriction data of
`AllCodimBlowupGlobalRestrictionData`: `Ã' → A'` and `B̃ → B` are the normalizations of the
reduced point closures, `α̃` and `g̃` the induced maps of normalizations, and `F''` a divisor of
`Ã'` dominating a divisor `D₁ = α̃(F'')` of `Ã`.

Discharged, as in the source: the discrete valuation rings at `F''`, `D₁` and `D̃ = g̃(D₁)`
(normal Noetherian stalks in codimension one), the commutative square, unramifiedness from
étaleness, the normalization of `A'` being an isomorphism at `F''` (étale over the regular `B'`,
hence `A'` normal there), `t` staying a uniformizer in `𝒪_{B̃,D̃}` (`B` regular at `D`, so the
normalization of `B` is an isomorphism there), and its nonzero image in `𝒪_{Ã,D₁}`.

Kept as hypotheses, as in the source: `B` regular at `D` and `B'` regular at `F` (the source gets
both from the excluded finite set), `f'|_{A'}` étale at `F'`, and the choices of the uniformizers
`t` and `t₁` and of `F''` over a divisor `D₁`.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

namespace BlowupRestrictionData

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {f : X ⟶ Y} [IsFinite f] [IsDominant f]
  {a : X} {b : Y} [Fact (genericPoint Y ∉ (pointCentre b).support)]
  (D : BlowupRestrictionData f a b)

/-- The normalization `Ã' ⟶ A'`. -/
abbrev ν : Palomar.normalization D.A' ⟶ D.A' := Palomar.normalizationMap D.A'

/-- The normalization `B̃ ⟶ B`. -/
abbrev νB : Palomar.normalization D.B ⟶ D.B := Palomar.normalizationMap D.B

/-- The lift `α̃ : Ã' ⟶ Ã` of `α|_{A'}` to normalizations. -/
abbrev αTilde : Palomar.normalization D.A' ⟶ Palomar.normalization D.A :=
  schemeDominantNormalizationMorphism D.αRestrict

/-- The lift `g̃ : Ã ⟶ B̃` of `g` to normalizations. -/
abbrev gTilde : Palomar.normalization D.A ⟶ Palomar.normalization D.B :=
  schemeDominantNormalizationMorphism D.g

/-- The square `q ∘ f'|_{A'} ∘ ν = ν_B ∘ g̃ ∘ α̃` of the display. -/
theorem normalized_square : (D.ν ≫ D.liftRestrict) ≫ D.q = D.αTilde ≫ (D.gTilde ≫ D.νB) := by
  rw [schemeDominantNormalizationMorphism_comp_normalizationMap, ← Category.assoc,
    schemeDominantNormalizationMorphism_comp_normalizationMap, Category.assoc, Category.assoc,
    ← D.square]

set_option maxHeartbeats 1600000 in
-- The statement synthesizes Noetherian, finiteness and DVR instances on four normalizations.
/-- **The display of `prop:bound-blowup`, on the actual `A'`, `B'`, `Ã'`.** For a divisor `F''`
of `Ã'` whose image `D₁ = α̃(F'')` is a divisor of `Ã`, with `F = f'(ν F'')` and
`D = q(F)`: if `B'` is regular at `F`, `B` is regular at `D`, and `f'|_{A'}` is étale at
`F' = ν F''`, then for a uniformizer `t` of `𝒪_{B,D}` and a uniformizer `t₁` of `𝒪_{Ã,D₁}`,
`v_F(q^* t) = v_{F''}(α̃^* g̃^* t) = e(D₁/D̃) · v_{F''}(α̃^* t₁)`.

`paper-p.tex` correspondence: Proposition 7.11 (`prop:bound-blowup`). -/
theorem boundBlowup_valuation_display (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s]
    (x : SchemeDivisorPoint (Palomar.normalization D.A'))
    (hD₁ : Order.coheight (D.αTilde x.1) = 1)
    [IsDiscreteValuationRing (D.B'.presheaf.stalk (D.liftRestrict (D.ν x.1)))]
    [IsDiscreteValuationRing (D.B.presheaf.stalk (D.q (D.liftRestrict (D.ν x.1))))]
    (hetale : (D.liftRestrict.stalkMap (D.ν x.1)).hom.FormallyEtale)
    (t : D.B.presheaf.stalk (D.q (D.liftRestrict (D.ν x.1)))) (ht : Irreducible t)
    {t₁ : (Palomar.normalization D.A).presheaf.stalk (D.αTilde x.1)} (ht₁ : Irreducible t₁) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
    letI : LocallyOfFiniteType (α f b ≫ f ≫ s) :=
      globalNormalizedBlowup_locallyOfFiniteType_over _ k (f ≫ s)
    letI : IsLocallyNoetherian (globalNormalizedBlowup ((pointCentre b).comap f)) :=
      LocallyOfFiniteType.isLocallyNoetherian (α f b ≫ f ≫ s)
    letI : IsFinite (Palomar.normalizationMap D.A') := Pcf.schemeGlobalNormalizationMap_isFinite _ k
      ((pointClosureIdealSheaf D.point).subschemeι ≫ α f b ≫ f ≫ s)
    letI : IsFinite (Palomar.normalizationMap D.A) := Pcf.schemeGlobalNormalizationMap_isFinite _ k
      ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
    letI : IsFinite (Palomar.normalizationMap D.B) := Pcf.schemeGlobalNormalizationMap_isFinite _ k
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
      ((maximalIdeal ((Palomar.normalization D.A).presheaf.stalk (D.αTilde x.1))).ramificationIdx
          ((Palomar.normalization D.B).presheaf.stalk (D.gTilde (D.αTilde x.1))) : ℕ∞) *
        addVal ((Palomar.normalization D.A').presheaf.stalk x.1) (D.αTilde.stalkMap x.1 t₁) := by
  intro D₁ tt
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ s)
  haveI : LocallyOfFiniteType (α f b ≫ f ≫ s) :=
    globalNormalizedBlowup_locallyOfFiniteType_over _ k (f ≫ s)
  haveI : IsLocallyNoetherian (globalNormalizedBlowup ((pointCentre b).comap f)) :=
    LocallyOfFiniteType.isLocallyNoetherian (α f b ≫ f ≫ s)
  haveI : LocallyOfFiniteType (β b ≫ s) := globalNormalizedBlowup_locallyOfFiniteType_over _ k s
  haveI : IsLocallyNoetherian (globalNormalizedBlowup (pointCentre b)) :=
    LocallyOfFiniteType.isLocallyNoetherian (β b ≫ s)
  haveI : IsFinite (Palomar.normalizationMap D.A') := Pcf.schemeGlobalNormalizationMap_isFinite _ k
    ((pointClosureIdealSheaf D.point).subschemeι ≫ α f b ≫ f ≫ s)
  haveI : IsFinite (Palomar.normalizationMap D.A) := Pcf.schemeGlobalNormalizationMap_isFinite _ k
    ((pointClosureIdealSheaf a).subschemeι ≫ f ≫ s)
  haveI : IsFinite (Palomar.normalizationMap D.B) := Pcf.schemeGlobalNormalizationMap_isFinite _ k
    ((pointClosureIdealSheaf b).subschemeι ≫ s)
  haveI : IsLocallyNoetherian (Palomar.normalization D.A') :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.A')
  haveI : IsLocallyNoetherian (Palomar.normalization D.A) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.A)
  haveI : IsLocallyNoetherian (Palomar.normalization D.B) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap D.B)
  haveI : IsDiscreteValuationRing ((Palomar.normalization D.A').presheaf.stalk x.1) :=
    x.stalk_isDiscreteValuationRing
  haveI : IsDiscreteValuationRing
      ((Palomar.normalization D.A).presheaf.stalk (D.αTilde x.1)) :=
    D₁.stalk_isDiscreteValuationRing
  haveI : IsFinite D.gTilde := inferInstance
  haveI : IsDiscreteValuationRing
      ((Palomar.normalization D.B).presheaf.stalk (D.gTilde (D.αTilde x.1))) :=
    (D₁.mapFiniteDominantNormal D.gTilde).stalk_isDiscreteValuationRing
  haveI := globalNormalizedBlowupMap_isFinite f (pointCentre b) k s
  haveI : IsFinite D.liftRestrict := pointClosureSubschemeMap_isFinite _ _ _ _
  haveI : LocallyOfFinitePresentation D.liftRestrict := inferInstance
  -- `f'|_{A'}` is formally unramified at `F'`.
  have hunr : (D.liftRestrict.stalkMap (D.ν x.1)).hom.FormallyUnramified := by
    letI := (D.liftRestrict.stalkMap (D.ν x.1)).hom.toAlgebra
    have h : Algebra.FormallyEtale _ _ := hetale
    exact (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp h).1
  -- `A'` is normal at `F'`, so its normalization is an isomorphism there.
  haveI : IsIntegrallyClosed (D.A'.presheaf.stalk (Palomar.normalizationMap D.A' x.1)) :=
    isIntegrallyClosed_stalk_of_formallyEtale_over_normalStalk D.liftRestrict _ inferInstance
      hetale
  have hν : IsIso (D.ν.stalkMap x.1) := inferInstance
  -- `B` is normal at `D`, so its normalization is an isomorphism at `D̃`.
  have hpt : D.q (D.liftRestrict (D.ν x.1)) = D.νB (D.gTilde (D.αTilde x.1)) := by
    have h := congrArg (fun φ ↦ φ x.1) D.normalized_square
    simpa only [Scheme.Hom.comp_apply] using h
  haveI : IsIntegrallyClosed
      (D.B.presheaf.stalk (Palomar.normalizationMap D.B (D.gTilde (D.αTilde x.1)))) :=
    isIntegrallyClosed_stalk_of_eq _ _ _ hpt.symm inferInstance
  have hνB : IsIso (D.νB.stalkMap (D.gTilde (D.αTilde x.1))) := inferInstance
  have htt : Irreducible tt := by
    let e := (D.B.presheaf.stalkCongr
      (.of_eq (congrArg (fun φ ↦ φ x.1) D.normalized_square))).commRingCatIsoToRingEquiv
    exact (MulEquiv.irreducible_iff e).mpr ht
  have ht' : Irreducible (D.νB.stalkMap (D.gTilde (D.αTilde x.1)) tt) := by
    let e := (asIso (D.νB.stalkMap (D.gTilde (D.αTilde x.1)))).commRingCatIsoToRingEquiv
    exact (MulEquiv.irreducible_iff e).mpr htt
  have ht0 : D.gTilde.stalkMap (D.αTilde x.1) (D.νB.stalkMap (D.gTilde (D.αTilde x.1)) tt) ≠ 0 := by
    intro h0
    have hinj := stalkMap_injective_of_dominant_integral D.gTilde (D.αTilde x.1)
    exact ht'.ne_zero (hinj (h0.trans (map_zero _).symm))
  exact BoundBlowupValuation.boundBlowup_valuation_identity_of_etale D.ν D.liftRestrict D.q
    D.αTilde D.gTilde D.νB D.normalized_square x.1 hunr hν t ht' ht0 ht₁

end BlowupRestrictionData

#print axioms BlowupRestrictionData.boundBlowup_valuation_display

end
end Pcf.Bounding.AllCodimBlowup
