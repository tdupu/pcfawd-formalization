/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalNormalizedLift
public import Pcf.Bounding.AllCodimBlowupIsoOffCentre
public import Pcf.Bounding.AllCodimBlowupMonodromyTransport
public import Pcf.Bounding.GlobalNormalizationNormal
public import Pcf.Bounding.PaperPBlowupBranch

/-!
# Monodromy and branch locus of the global normalized blow-up

This is `latex/paper-p.tex`, Proposition `prop:normalized-blowup-branch`, for
the global normalized blow-up `f' : X' ⟶ Y'` of a finite dominant morphism of
normal integral schemes of finite type over a field:

* the natural maps `α : X' ⟶ X` and `β : Y' ⟶ Y` are isomorphisms on generic
  stalks, so `f'` has the generic monodromy of `f`;
* over the complement of the centre, `α` and `β` are isomorphisms on stalks,
  so a codimension-one non-étale point `w` of `f'` whose image avoids
  `β⁻¹(B)` lies over a codimension-one non-étale point `α w` of `f`, with
  `β (f' w) = f (α w)`. This is the strict-transform clause.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

/-- If `f` is bijective on the stalk at `x` and `f ≫ g` is too, then `g` is
bijective on the stalk at `f x`. -/
theorem stalkMap_bijective_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : Function.Bijective (f.stalkMap x).hom)
    (hfg : Function.Bijective ((f ≫ g).stalkMap x).hom) :
    Function.Bijective (g.stalkMap (f x)).hom := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, RingHom.coe_comp] at hfg
  exact (Function.Bijective.of_comp_iff' hf _).mp hfg

theorem stalkMap_bijective_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : Function.Bijective (f.stalkMap x).hom)
    (hg : Function.Bijective (g.stalkMap (f x)).hom) :
    Function.Bijective ((f ≫ g).stalkMap x).hom := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hf.comp hg

theorem stalkMap_bijective_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (x : X)
    (hg : Function.Bijective (g.stalkMap x).hom) :
    Function.Bijective (f.stalkMap x).hom := by
  rw [Scheme.Hom.stalkMap_congr_hom f g h x, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hg.comp (ConcreteCategory.bijective_of_isIso _)

theorem stalkMap_bijective_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : Function.Bijective (f.stalkMap x).hom :=
  ConcreteCategory.bijective_of_isIso _

/-- The stalks of a normal integral scheme are integrally closed. -/
theorem isNormalScheme_stalk_integrallyClosed {X : Scheme.{u}} [IsIntegral X]
    [IsNormalScheme X] (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨_, hxU⟩⟩
  let xU : U := ⟨x, hxU⟩
  let : IsIntegrallyClosed Γ(X, U) := IsNormalScheme.component_integrallyClosed ⟨U, hU⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk _ xU
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf xU).asIdeal :=
    hU.isLocalization_stalk xU
  exact isIntegrallyClosed_of_isLocalization _ _
    (hU.primeIdealOf xU).asIdeal.primeCompl_le_nonZeroDivisors

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- **The global Rees blow-up is an isomorphism off the centre, on stalks.**

**Divergence from Stacks 02OS:** only part (1), and only its stalkwise form at
points over the complement of the centre, on an integral base.

`paper-p.tex` correspondence: Proposition 7.9 (`prop:normalized-blowup-branch`). -/
@[stacks 02OS "part (1), stalkwise, integral base"]
theorem globalReesToBase_stalkMap_bijective (I : Y.IdealSheafData) (x : globalRees I)
    (hx : globalReesToBase I x ∉ I.support) :
    Function.Bijective ((globalReesToBase I).stalkMap x).hom := by
  obtain ⟨U, x₀, rfl⟩ := exists_globalReesChart I x
  have hU := globalReesChart_nonempty I U _ ⟨x₀, rfl⟩
  haveI : Nonempty U.1 := hU.to_subtype
  apply stalkMap_bijective_of_comp (globalReesChart I U) (globalReesToBase I) x₀
    (stalkMap_bijective_of_isOpenImmersion _ x₀)
  apply stalkMap_bijective_congr (globalReesChart_toBase' I U) x₀
  apply stalkMap_bijective_comp _ _ x₀ _ (stalkMap_bijective_of_isOpenImmersion _ _)
  apply reesProjToSpec_stalkMap_bijective
  intro hle
  apply hx
  have hmem : globalReesToBase I (globalReesChart I U x₀) ∈ U.1 :=
    (mem_range_globalReesChart_iff I U _).mp ⟨x₀, rfl⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem, Scheme.mem_zeroLocus_iff]
  intro s hs hbasic
  have hpt : globalReesToBase I (globalReesChart I U x₀) =
      U.2.fromSpec (reesProjToSpec (I.ideal U) x₀) := by
    rw [← Scheme.Hom.comp_apply, globalReesChart_toBase', Scheme.Hom.comp_apply]
    rfl
  rw [hpt, ← Scheme.Hom.mem_preimage, U.2.fromSpec_preimage_basicOpen] at hbasic
  exact hbasic (hle hs)

variable (I : Y.IdealSheafData) [hI : Fact (genericPoint Y ∉ I.support)]

/-- **The global normalized blow-up of a normal scheme is an isomorphism off
the centre, on stalks.**

`paper-p.tex` correspondence: Proposition 7.9 (`prop:normalized-blowup-branch`). -/
theorem globalNormalizedBlowupToBase_stalkMap_bijective [IsNormalScheme Y]
    (y : globalNormalizedBlowup I) (hy : globalNormalizedBlowupToBase I y ∉ I.support) :
    Function.Bijective ((globalNormalizedBlowupToBase I).stalkMap y).hom := by
  have hrees := globalReesToBase_stalkMap_bijective I (Palomar.normalizationMap _ y) hy
  apply stalkMap_bijective_comp _ _ y _ hrees
  haveI := isNormalScheme_stalk_integrallyClosed (globalReesToBase I (Palomar.normalizationMap _ y))
  haveI : IsIntegrallyClosed ((globalRees I).presheaf.stalk (Palomar.normalizationMap _ y)) :=
    IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective _ hrees)
  exact stalkMap_bijective_of_isIntegralHom_of_integrallyClosed _ y
    (Pcf.schemeGlobalNormalizationMap_stalkBirationalAt _ y) inferInstance

/-- The natural map `β : Y' ⟶ Y` is an isomorphism on generic stalks. -/
instance globalNormalizedBlowupToBase_genericStalk_isIso :
    IsIso ((globalNormalizedBlowupToBase I).stalkMap
      (genericPoint (globalNormalizedBlowup I))) := by
  haveI := globalReesToBase_isDominant I hI.out
  have hsurj : Function.Surjective
      (Pcf.schemeGenericFieldHom (globalNormalizedBlowupToBase I)) := by
    have h' := Pcf.schemeGenericFieldHom_congr (φ := globalNormalizedBlowupToBase I)
      (ψ := Palomar.normalizationMap (globalRees I) ≫ globalReesToBase I) rfl
    rw [h', Pcf.schemeGenericFieldHom_comp]
    exact (schemeGenericFieldHom_surjective_of_isIso
      (Palomar.normalizationMap (globalRees I))).comp
      (globalReesToBase_genericField_surjective I hI.out)
  have hbij : Function.Bijective
      (Pcf.schemeGenericFieldHom (globalNormalizedBlowupToBase I)) :=
    ⟨RingHom.injective _, hsurj⟩
  rw [Pcf.schemeGenericFieldHom_eq_stalkCongr, RingHom.coe_comp] at hbij
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ (RingEquiv.bijective _)).mp hbij

section Map

variable {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) [IsFinite f] [IsDominant f]

/-- `prop:normalized-blowup-branch`, monodromy clause: the global normalized
blow-up has the generic monodromy of `f`.

`paper-p.tex` correspondence: Proposition 7.9 (`prop:normalized-blowup-branch`). -/
theorem globalNormalizedBlowupMap_primeToPMonodromy (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (p : ℕ)
    (hmono : Pcf.IsPrimeToPMonodromyMap p f) :
    letI := globalNormalizedBlowupMap_isFinite f I k s
    Pcf.IsPrimeToPMonodromyMap p (globalNormalizedBlowupMap f I) := by
  letI := globalNormalizedBlowupMap_isFinite f I k s
  exact primeToPMonodromy_of_genericBirationalSquare p f (globalNormalizedBlowupMap f I)
    (globalNormalizedBlowupToBase (I.comap f)) (globalNormalizedBlowupToBase I)
    (globalNormalizedBlowupMap_comm f I) hmono

variable [IsNormalScheme X] [IsNormalScheme Y]

/-- Off the centre, formal étaleness of the global normalized blow-up at a
point is formal étaleness of `f` at its image. -/
theorem globalNormalizedBlowupMap_formallyEtale_iff_offCentre
    (w : globalNormalizedBlowup (I.comap f))
    (hw : globalNormalizedBlowupToBase I (globalNormalizedBlowupMap f I w) ∉ I.support) :
    ((globalNormalizedBlowupMap f I).stalkMap w).hom.FormallyEtale ↔
      (f.stalkMap (globalNormalizedBlowupToBase (I.comap f) w)).hom.FormallyEtale := by
  have hcomm := globalNormalizedBlowupMap_comm f I
  have hpt : globalNormalizedBlowupToBase I (globalNormalizedBlowupMap f I w) =
      f (globalNormalizedBlowupToBase (I.comap f) w) := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have hα : globalNormalizedBlowupToBase (I.comap f) w ∉ (I.comap f).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change f _ ∉ I.support
    rwa [← hpt]
  exact formallyEtale_stalkMap_iff_of_square _ _ _ f hcomm w
    (globalNormalizedBlowupToBase_stalkMap_bijective (I.comap f) w hα)
    (globalNormalizedBlowupToBase_stalkMap_bijective I _ hw)

/-- `prop:normalized-blowup-branch`, branch clause off the exceptional locus:
a codimension-one point of `X'` at which the normalized blow-up is not
formally étale, and whose image in `Y'` lies outside `β⁻¹(B)`, is a
codimension-one non-étale point `α w` of `f`, and its image in `Y'` lies over
`f (α w)`.

`paper-p.tex` correspondence: Proposition 7.9 (`prop:normalized-blowup-branch`). -/
theorem globalNormalizedBlowupMap_branch_offCentre
    (w : globalNormalizedBlowup (I.comap f)) (hcodim : Order.coheight w = 1)
    (hw : globalNormalizedBlowupToBase I (globalNormalizedBlowupMap f I w) ∉ I.support)
    (hbranch : ¬ ((globalNormalizedBlowupMap f I).stalkMap w).hom.FormallyEtale) :
    ∃ d : SchemeDivisorPoint X,
      d.1 = globalNormalizedBlowupToBase (I.comap f) w ∧
      d ∈ schemeDivisorNonEtaleLocus f ∧
      globalNormalizedBlowupToBase I (globalNormalizedBlowupMap f I w) = f d.1 := by
  have hcomm := globalNormalizedBlowupMap_comm f I
  have hpt : globalNormalizedBlowupToBase I (globalNormalizedBlowupMap f I w) =
      f (globalNormalizedBlowupToBase (I.comap f) w) := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have hα : globalNormalizedBlowupToBase (I.comap f) w ∉ (I.comap f).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change f _ ∉ I.support
    rwa [← hpt]
  have hbij := globalNormalizedBlowupToBase_stalkMap_bijective (I.comap f) w hα
  let d : SchemeDivisorPoint X :=
    ⟨globalNormalizedBlowupToBase (I.comap f) w,
      (coheight_eq_of_stalkMap_bijective _ w hbij).symm ▸ hcodim⟩
  exact ⟨d, rfl, (globalNormalizedBlowupMap_formallyEtale_iff_offCentre I f w hw).not.mp hbranch,
    hpt⟩

end Map

#print axioms globalReesToBase_stalkMap_bijective
#print axioms globalNormalizedBlowupToBase_stalkMap_bijective
#print axioms globalNormalizedBlowupMap_primeToPMonodromy
#print axioms globalNormalizedBlowupMap_branch_offCentre

end
end Pcf.Bounding.AllCodimBlowup
