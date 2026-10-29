/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalRees
public import Pcf.Bounding.AllCodimBlowupAbsoluteNormalization
public import Pcf.Bounding.GlobalNormalizationMorphism
public import Pcf.Bounding.GlobalNormalizationFinite
public import Pcf.Bounding.AllCodimBlowupExceptionalSurjectivity
public import Pcf.Bounding.AllCodimBlowupGenericStalk

/-!
# The global Rees blow-up as a named scheme, and its normalization

`globalReesBlowupExistence` only asserts that a global Rees blow-up exists.
This file names the canonical glued scheme `globalRees I`, its structure map
and its Cartesian affine charts. For an integral base and an ideal sheaf whose
support misses the generic point, the global Rees blow-up is integral; over a
locally Noetherian base it is locally of finite type, hence locally of finite
type over a field when the base is. The global normalized blow-up of
`latex/paper-p.tex`, Definition `def:normalized-blowup-data`, is then the
absolute normalization `Palomar.normalization (globalRees I)`, which is finite
over the global Rees blow-up in the finite-type case.
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

/-- The canonical global Rees blow-up of an ideal sheaf: the relative gluing
of the actual affine Rees `Proj`s over all affine opens.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
abbrev globalRees (I : Y.IdealSheafData) : Scheme.{u} :=
  (canonicalReesRelativeGluingData I).glued

/-- The structure map of the global Rees blow-up. -/
def globalReesToBase (I : Y.IdealSheafData) : globalRees I ⟶ Y :=
  (canonicalReesRelativeGluingData I).toBase

/-- The affine Rees chart over an affine open. -/
def globalReesChart (I : Y.IdealSheafData) (U : Y.affineOpens) :
    reesProj (I.ideal U) ⟶ globalRees I :=
  colimit.ι (canonicalReesRelativeGluingData I).functor U

/-- Every affine Rees chart is the base change of its affine open.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
theorem globalReesChart_isPullback (I : Y.IdealSheafData) (U : Y.affineOpens) :
    IsPullback (affineReesToOpen I U) (globalReesChart I U) U.1.ι (globalReesToBase I) :=
  (canonicalReesRelativeGluingData I).isPullback_natTrans_ι_toBase U

@[reassoc]
theorem globalReesChart_toBase (I : Y.IdealSheafData) (U : Y.affineOpens) :
    globalReesChart I U ≫ globalReesToBase I = affineReesToOpen I U ≫ U.1.ι :=
  (globalReesChart_isPullback I U).w.symm

@[reassoc]
theorem globalReesChart_toBase' (I : Y.IdealSheafData) (U : Y.affineOpens) :
    globalReesChart I U ≫ globalReesToBase I = reesProjToSpec (I.ideal U) ≫ U.2.fromSpec := by
  rw [globalReesChart_toBase, affineReesToOpen, Category.assoc, IsAffineOpen.isoSpec_inv_ι]

instance globalReesChart_isOpenImmersion (I : Y.IdealSheafData) (U : Y.affineOpens) :
    IsOpenImmersion (globalReesChart I U) :=
  MorphismProperty.of_isPullback (globalReesChart_isPullback I U) inferInstance

@[reassoc (attr := simp)]
theorem globalReesChart_transition (I : Y.IdealSheafData) {U V : Y.affineOpens} (h : U ⟶ V) :
    affineReesTransition I h ≫ globalReesChart I V = globalReesChart I U :=
  colimit.w (canonicalReesRelativeGluingData I).functor h

theorem globalReesToBase_preimage (I : Y.IdealSheafData) (U : Y.affineOpens) :
    globalReesToBase I ⁻¹ᵁ U.1 = (globalReesChart I U).opensRange := by
  have h := (canonicalReesRelativeGluingData I).toBase_preimage_eq_opensRange_ι U
  rw [show (Y.directedAffineCover.f U).opensRange = U.1 from U.1.opensRange_ι] at h
  exact h

theorem mem_range_globalReesChart_iff (I : Y.IdealSheafData) (U : Y.affineOpens)
    (x : globalRees I) :
    x ∈ Set.range (globalReesChart I U) ↔ globalReesToBase I x ∈ U.1 := by
  have := congrArg (fun W : (globalRees I).Opens ↦ x ∈ W) (globalReesToBase_preimage I U)
  simp only [eq_iff_iff] at this
  exact this.symm.trans (by rfl)

/-- A point of the global Rees blow-up lies in the chart over an affine open
containing its image. -/
theorem exists_globalReesChart (I : Y.IdealSheafData) (x : globalRees I) :
    ∃ U : Y.affineOpens, x ∈ Set.range (globalReesChart I U) := by
  obtain ⟨U, hU⟩ := Y.directedAffineCover.exists_eq (globalReesToBase I x)
  refine ⟨U, (mem_range_globalReesChart_iff I U x).mpr ?_⟩
  obtain ⟨y, hy⟩ := hU
  rw [← hy]
  exact y.2

/-- `reesProjToSpec_isProper` without the unused domain hypothesis. -/
theorem reesProjToSpec_isProper' {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    IsProper (reesProjToSpec I) := by
  haveI : Algebra.FiniteType (reesGrade I 0) (reesAlgebra I) :=
    reesAlgebra_finiteType_over_zeroGrade I hI
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (reesGradeZeroMap I))) := by
    apply IsClosedImmersion.spec_of_surjective
    exact reesGradeZeroMap_surjective I
  unfold reesProjToSpec reesProj
  infer_instance

/-- The global Rees blow-up is locally of finite type over a locally
Noetherian base. -/
theorem globalReesToBase_locallyOfFiniteType [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) : LocallyOfFiniteType (globalReesToBase I) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType)
    Y.directedAffineCover]
  intro U
  have h := (globalReesChart_isPullback I U).flip
  haveI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have hfg : (I.ideal U).FG := IsNoetherian.noetherian _
  letI : IsProper (reesProjToSpec (I.ideal U)) := reesProjToSpec_isProper' _ hfg
  change LocallyOfFiniteType (pullback.snd (globalReesToBase I) U.1.ι)
  rw [← h.isoPullback_inv_snd]
  dsimp only [affineReesToOpen]
  infer_instance

/-- The global Rees blow-up of a locally finite-type field scheme is locally
of finite type over the field. -/
theorem globalRees_locallyOfFiniteType_over (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) : LocallyOfFiniteType (globalReesToBase I ≫ s) := by
  letI := globalReesToBase_locallyOfFiniteType I
  infer_instance


section Integral

variable [IsIntegral Y]

theorem genericPoint_mem_affineOpen (U : Y.affineOpens) (hU : (U.1 : Set Y).Nonempty) :
    genericPoint Y ∈ U.1 :=
  ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr (by simpa using hU)

/-- If the support of an ideal sheaf misses the generic point, then its
ideal on every nonempty affine open contains a nonzero element. -/
theorem exists_ne_zero_mem_ideal (I : Y.IdealSheafData) (hI : genericPoint Y ∉ I.support)
    (U : Y.affineOpens) (hU : (U.1 : Set Y).Nonempty) :
    ∃ a : I.ideal U, (a : Γ(Y, U.1)) ≠ 0 := by
  have hgen := genericPoint_mem_affineOpen U hU
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hgen, Scheme.mem_zeroLocus_iff] at hI
  push Not at hI
  obtain ⟨f, hf, hx⟩ := hI
  refine ⟨⟨f, hf⟩, fun h0 ↦ ?_⟩
  change f = 0 at h0
  subst h0
  rw [Scheme.basicOpen_zero] at hx
  exact hx

/-- Each chart over a nonempty affine open is integral. -/
theorem reesProj_isIntegral_of_nonempty (I : Y.IdealSheafData)
    (hI : genericPoint Y ∉ I.support) (U : Y.affineOpens) (hU : (U.1 : Set Y).Nonempty) :
    IsIntegral (reesProj (I.ideal U)) := by
  haveI : Nonempty U.1 := hU.to_subtype
  obtain ⟨a, ha⟩ := exists_ne_zero_mem_ideal I hI U hU
  exact reesProj_isIntegral (I.ideal U) a ha

omit [IsIntegral Y] in
theorem globalReesChart_nonempty (I : Y.IdealSheafData) (U : Y.affineOpens)
    (x : globalRees I) (hx : x ∈ Set.range (globalReesChart I U)) :
    (U.1 : Set Y).Nonempty :=
  ⟨_, (mem_range_globalReesChart_iff I U x).mp hx⟩

/-- The global Rees blow-up of an integral scheme along an ideal sheaf whose
support misses the generic point is irreducible. -/
theorem globalRees_irreducibleSpace (I : Y.IdealSheafData) (hI : genericPoint Y ∉ I.support) :
    IrreducibleSpace (globalRees I) := by
  have hrange (U : Y.affineOpens) (hU : (U.1 : Set Y).Nonempty) :
      IsIrreducible (Set.range (globalReesChart I U)) := by
    letI := reesProj_isIntegral_of_nonempty I hI U hU
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (globalReesChart I U).continuous.continuousOn
  have hsub (U V : Y.affineOpens) (h : U.1 ≤ V.1) :
      Set.range (globalReesChart I U) ⊆ Set.range (globalReesChart I V) := by
    intro x hx
    rw [mem_range_globalReesChart_iff] at hx ⊢
    exact h hx
  have hopen (U : Y.affineOpens) : IsOpen (Set.range (globalReesChart I U)) :=
    (globalReesChart I U).isOpenEmbedding.isOpen_range
  -- a common nonempty affine open inside two nonempty affine opens
  have hcommon (U V : Y.affineOpens) (hU : (U.1 : Set Y).Nonempty)
      (hV : (V.1 : Set Y).Nonempty) :
      ∃ W : Y.affineOpens, W.1 ≤ U.1 ∧ W.1 ≤ V.1 ∧ (W.1 : Set Y).Nonempty := by
    obtain ⟨W, hW, hgW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show genericPoint Y ∈ U.1 ⊓ V.1 from
        ⟨genericPoint_mem_affineOpen U hU, genericPoint_mem_affineOpen V hV⟩)
    exact ⟨⟨W, hW⟩, hWle.trans inf_le_left, hWle.trans inf_le_right, ⟨_, hgW⟩⟩
  have hnonempty (U : Y.affineOpens) (hU : (U.1 : Set Y).Nonempty) :
      (Set.range (globalReesChart I U)).Nonempty := by
    letI := reesProj_isIntegral_of_nonempty I hI U hU
    exact Set.range_nonempty _
  obtain ⟨U₀, hU₀, hgU₀, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  let A₀ : Y.affineOpens := ⟨U₀, hU₀⟩
  have hA₀ : (A₀.1 : Set Y).Nonempty := ⟨_, hgU₀⟩
  have hall : (Set.univ : Set (globalRees I)) ⊆ closure (Set.range (globalReesChart I A₀)) := by
    intro x _
    obtain ⟨V, hxV⟩ := exists_globalReesChart I x
    have hV := globalReesChart_nonempty I V x hxV
    obtain ⟨W, hWU, hWV, hW⟩ := hcommon A₀ V hA₀ hV
    have hinter : (Set.range (globalReesChart I V) ∩ Set.range (globalReesChart I W)).Nonempty := by
      obtain ⟨z, hz⟩ := hnonempty W hW
      exact ⟨z, hsub W V hWV hz, hz⟩
    have := subset_closure_inter_of_isPreirreducible_of_isOpen (hrange V hV).isPreirreducible
      (hopen W) hinter hxV
    exact closure_mono (Set.inter_subset_right.trans (hsub W A₀ hWU)) this
  have huniv : closure (Set.range (globalReesChart I A₀)) = Set.univ :=
    Set.eq_univ_of_univ_subset hall
  have h := (hrange A₀ hA₀).closure
  rw [huniv] at h
  exact (irreducibleSpace_def _).mpr h


/-- The global Rees blow-up of an integral scheme along an ideal sheaf whose
support misses the generic point is reduced: its stalks are stalks of reduced
affine Rees charts. -/
theorem globalRees_isReduced (I : Y.IdealSheafData) (hI : genericPoint Y ∉ I.support) :
    IsReduced (globalRees I) := by
  have (x : globalRees I) : _root_.IsReduced ((globalRees I).presheaf.stalk x) := by
    obtain ⟨V, y, rfl⟩ := exists_globalReesChart I x
    have hV := globalReesChart_nonempty I V _ ⟨y, rfl⟩
    letI := reesProj_isIntegral_of_nonempty I hI V hV
    have e := asIso ((globalReesChart I V).stalkMap y)
    exact isReduced_of_injective e.commRingCatIsoToRingEquiv
      e.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/-- The global Rees blow-up is integral.

**Divergence from Stacks 02ND:** the ideal sheaf is assumed to have support
missing the generic point, which on an integral scheme is the nonzero
condition; only integrality of the canonical glued Rees scheme is asserted.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
@[stacks 02ND "support of the ideal sheaf misses the generic point"]
theorem globalRees_isIntegral (I : Y.IdealSheafData) (hI : genericPoint Y ∉ I.support) :
    IsIntegral (globalRees I) := by
  letI := globalRees_isReduced I hI
  letI := globalRees_irreducibleSpace I hI
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance globalRees_isIntegral_of_fact (I : Y.IdealSheafData)
    [hI : Fact (genericPoint Y ∉ I.support)] : IsIntegral (globalRees I) :=
  globalRees_isIntegral I hI.out

/-- The global Rees blow-up is dominant over an integral base. -/
theorem globalReesToBase_isDominant (I : Y.IdealSheafData) (hI : genericPoint Y ∉ I.support) :
    IsDominant (globalReesToBase I) := by
  obtain ⟨U₀, hU₀, hgU₀, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  let A₀ : Y.affineOpens := ⟨U₀, hU₀⟩
  have hA₀ : (A₀.1 : Set Y).Nonempty := ⟨_, hgU₀⟩
  haveI : Nonempty A₀.1 := hA₀.to_subtype
  obtain ⟨a, ha⟩ := exists_ne_zero_mem_ideal I hI A₀ hA₀
  haveI := reesProjToSpec_isDominant (I.ideal A₀) a ha
  haveI : Nonempty (Spec Γ(Y, A₀.1)) := ⟨A₀.2.isoSpec.hom ⟨_, hgU₀⟩⟩
  haveI : IsDominant A₀.2.fromSpec :=
    ⟨A₀.2.fromSpec.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  haveI : IsDominant (globalReesChart I A₀ ≫ globalReesToBase I) := by
    rw [globalReesChart_toBase']
    infer_instance
  exact IsDominant.of_comp (globalReesChart I A₀) _

end Integral

section Normalized

variable [IsIntegral Y] (I : Y.IdealSheafData) [Fact (genericPoint Y ∉ I.support)]

/-- The normalized blow-up `Y'` of `Y` along the centre `I`, as in
`latex/paper-p.tex`, Definition `def:normalized-blowup-data`: the absolute
normalization of the global Rees blow-up `Bl_I(Y)`.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
abbrev globalNormalizedBlowup : Scheme.{u} :=
  Palomar.normalization (globalRees I)

/-- The natural map `β : Y' ⟶ Y`.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
def globalNormalizedBlowupToBase : globalNormalizedBlowup I ⟶ Y :=
  Palomar.normalizationMap (globalRees I) ≫ globalReesToBase I

instance globalNormalizedBlowupToBase_isDominant :
    IsDominant (globalNormalizedBlowupToBase I) := by
  haveI := globalReesToBase_isDominant I (Fact.out)
  dsimp only [globalNormalizedBlowupToBase]
  infer_instance

/-- Over a scheme locally of finite type over a field, the normalization of
the global Rees blow-up is finite over it. -/
theorem globalRees_normalizationMap_isFinite (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] :
    IsFinite (Palomar.normalizationMap (globalRees I)) := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  haveI := globalRees_locallyOfFiniteType_over k s I
  exact Pcf.schemeGlobalNormalizationMap_isFinite (globalRees I) k (globalReesToBase I ≫ s)

/-- The normalized blow-up is locally of finite type over the field. -/
theorem globalNormalizedBlowup_locallyOfFiniteType_over (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] :
    LocallyOfFiniteType (globalNormalizedBlowupToBase I ≫ s) := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  haveI := globalReesToBase_locallyOfFiniteType I
  haveI := globalRees_normalizationMap_isFinite I k s
  dsimp only [globalNormalizedBlowupToBase]
  infer_instance

/-- The normalized blow-up is a normal integral scheme. -/
instance globalNormalizedBlowup_isNormalScheme : IsNormalScheme (globalNormalizedBlowup I) :=
  inferInstance

end Normalized

#print axioms globalReesChart_isPullback
#print axioms globalReesToBase_locallyOfFiniteType
#print axioms exists_globalReesChart
#print axioms globalRees_irreducibleSpace
#print axioms globalRees_isIntegral
#print axioms globalReesToBase_isDominant
#print axioms globalRees_normalizationMap_isFinite
#print axioms globalNormalizedBlowup_locallyOfFiniteType_over

end
end Pcf.Bounding.AllCodimBlowup
