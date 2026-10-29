/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingTameStalkTransport
public import Pcf.Bounding.DivisorFlagCodimension

/-!
# Positive-characteristic pointwise bounding on the original divisor

For `latex/paper-p.tex`, Theorem `thm:bounding`, this proves the pointwise
étaleness of the original reduced divisor restriction above every divisor
generic point outside the manuscript's exact exceptional set `Σ`. The tame
chart uses prime-to-characteristic monodromy; regularity and branch avoidance
come directly from the three components defining `Σ`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- At every specified source point above a good target divisor point, the
actual finite map of original reduced divisor closures has a formally étale
stalk. No source point is selected by a choice in the statement.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharP_at_formallyEtale
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hxz : A.closureMapFiniteDominantNormal f x = z.1) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    z.1 ∉ paperPBoundingSigma f (A.mapFiniteDominantNormal f) →
      ((A.closureMapFiniteDominantNormal f).stalkMap x).hom.FormallyEtale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  intro hz
  let B := A.mapFiniteDominantNormal f
  let I := pointClosureIdealSheaf A.1
  let J := pointClosureIdealSheaf B.1
  have hsource : A.1 ⤳ I.subschemeι x := pointClosure_specializes A.1 x
  have htargeteq : J.subschemeι z.1 = f (I.subschemeι x) := by
    have hsquare := pointClosureSubschemeMap_subschemeι f A.1 B.1 rfl
    have hpoint := congrArg (fun g : I.subscheme ⟶ Y => g x) hsquare
    change J.subschemeι (A.closureMapFiniteDominantNormal f x) =
      f (I.subschemeι x) at hpoint
    rw [hxz] at hpoint
    exact hpoint
  have hcohtarget : Order.coheight (J.subschemeι z.1) = 2 :=
    B.closureDivisor_coheight_of_finiteType k s z
  have hcohsource : Order.coheight (I.subschemeι x) = 2 := by
    rw [← coheight_apply_eq_of_finite_dominant_normal f (I.subschemeι x),
      ← htargeteq]
    exact hcohtarget
  have hregular := paperPBoundingSigma_regular_at f B z.1 hz
  have hprincipal : (stalkGenerizationPrime Y (hsource.map f.continuous)).IsPrincipal := by
    have hZ : ∀ h' : B.1 ⤳ J.subschemeι z.1,
        (stalkGenerizationPrime Y h').IsPrincipal := by
      intro h'
      exact paperPBounding_regularFlag_stalkGenerizationPrime_principal
        B z h' hcohtarget hregular.1 hregular.2
    have hF : ∀ h' : B.1 ⤳ f (I.subschemeι x),
        (stalkGenerizationPrime Y h').IsPrincipal := htargeteq ▸ hZ
    exact hF (hsource.map f.continuous)
  have hdvr : IsDiscreteValuationRing
      (closureStalk Y (hsource.map f.continuous)) := by
    have hZ : ∀ h' : B.1 ⤳ J.subschemeι z.1,
        IsDiscreteValuationRing (closureStalk Y h') := by
      intro h'
      exact paperPBounding_regularDivisor_closureStalk_dvr B z h' hregular.2
    have hF : ∀ h' : B.1 ⤳ f (I.subschemeι x),
        IsDiscreteValuationRing (closureStalk Y h') := htargeteq ▸ hZ
    exact hF (hsource.map f.continuous)
  have hunram : ∀ w : SchemeDivisorPoint X,
      f w.1 ⤳ f (I.subschemeι x) → f w.1 ≠ f A.1 →
        (f.stalkMap w.1).hom.FormallyEtale := by
    intro w hw hneq
    apply paperPBoundingSigma_otherBranch_formallyEtale f B z.1 hz w
    · exact htargeteq.symm ▸ hw
    · exact hneq
  exact pointClosureSubschemeMap_formallyEtale_of_tameChart p hp k s f hmono
    A x hsource hcohsource hprincipal hdvr hunram

/-- The pointwise stalk result gives actual étale neighborhoods for the
original reduced restriction. Finiteness supplies local finite presentation.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharP_at_etaleNeighborhood
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hxz : A.closureMapFiniteDominantNormal f x = z.1) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    let g := A.closureMapFiniteDominantNormal f
    z.1 ∉ paperPBoundingSigma f (A.mapFiniteDominantNormal f) →
      ∃ (U : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme.Opens)
        (_ : IsAffineOpen U)
        (V : (pointClosureIdealSheaf A.1).subscheme.Opens)
        (_ : IsAffineOpen V)
        (hVU : V ≤ g ⁻¹ᵁ U),
        x ∈ V ∧ (g.appLE U V hVU).hom.Etale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  let g := A.closureMapFiniteDominantNormal f
  dsimp only
  intro hz
  letI : IsFinite g := pointClosureSubschemeMap_isFinite f A.1
    (A.mapFiniteDominantNormal f).1 rfl
  letI : LocallyOfFinitePresentation g := by infer_instance
  exact exists_etale_of_formallyEtale_stalk g x
    (paperPBoundingCharP_at_formallyEtale p hp k s f hmono A x z hxz hz)

#print axioms paperPBoundingCharP_at_formallyEtale
#print axioms paperPBoundingCharP_at_etaleNeighborhood

end
end Pcf
