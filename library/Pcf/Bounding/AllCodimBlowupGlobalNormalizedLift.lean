/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalReesLift
public import Pcf.Bounding.AllCodimBlowupNormalizedLift
public import Pcf.Bounding.AllCodimBlowupGenericStalkComparison
public import Pcf.Bounding.PaperPBlowupConstructionAffine
public import Pcf.Bounding.PaperPBlowupNormalizedSquare
public import Pcf.Bounding.PrimaryFibresScheme

/-!
# The global normalized blow-up of a finite morphism

Let `f : X ⟶ Y` be a finite dominant morphism of integral schemes, locally of
finite type over a field, and let `I` be an ideal sheaf on `Y` whose support
misses the generic point. The global Rees blow-up of the scheme-theoretic
inverse image `I.comap f` maps finitely and dominantly to the global Rees
blow-up of `I`. Its lift to absolute normalizations is the unique finite
surjective morphism `f' : X' ⟶ Y'` with `β ∘ f' = f ∘ α`.

This is `latex/paper-p.tex`, Proposition `prop:normalized-blowup-construction`,
for the global normalized blow-ups of Definition `def:normalized-blowup-data`.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

section ReesMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (I : Y.IdealSheafData)

/-- The global map of Rees blow-ups `Bl_{f⁻¹I}(X) ⟶ Bl_I(Y)`.

`paper-p.tex` correspondence: Proposition 7.7 (`prop:normalized-blowup-construction`). -/
def globalReesMap : globalRees (I.comap f) ⟶ globalRees I :=
  inv (liftReesComparison f I) ≫ liftReesMap f I

@[reassoc (attr := simp)]
theorem globalReesMap_toBase :
    globalReesMap f I ≫ globalReesToBase I = globalReesToBase (I.comap f) ≫ f := by
  rw [globalReesMap, Category.assoc, liftReesMap_toBase, ← liftReesComparison_toBase,
    IsIso.inv_hom_id_assoc]

/-- On the chart over the preimage of an affine open, the global Rees map is
the extended affine Rees map. -/
@[reassoc]
theorem globalReesChart_globalReesMap (U : Y.affineOpens) :
    globalReesChart (I.comap f) (preimageAffine f U) ≫ globalReesMap f I =
      inv (liftReesComparisonApp f I U) ≫ liftReesMapApp f I U ≫ globalReesChart I U := by
  have h : globalReesChart (I.comap f) (preimageAffine f U) =
      inv (liftReesComparisonApp f I U) ≫ liftReesChart f I U ≫ liftReesComparison f I := by
    rw [liftReesChart_comparison, IsIso.inv_hom_id_assoc]
  rw [globalReesMap, h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, liftReesChart_map]

set_option linter.overlappingInstances false in
/-- The global map of Rees blow-ups of a finite morphism is finite. -/
instance globalReesMap_isFinite [IsFinite f] : IsFinite (globalReesMap f I) := by
  haveI := liftReesMap_isFinite f I
  dsimp only [globalReesMap]
  infer_instance

end ReesMap

section Integral

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem genericPoint_not_mem_comap_support (f : X ⟶ Y) [IsDominant f]
    (I : Y.IdealSheafData) (hI : genericPoint Y ∉ I.support) :
    genericPoint X ∉ (I.comap f).support := by
  rw [Scheme.IdealSheafData.support_comap]
  change f (genericPoint X) ∉ I.support
  rwa [map_genericPoint_eq_of_isDominant f]

instance fact_genericPoint_not_mem_comap_support (f : X ⟶ Y) [IsDominant f]
    (I : Y.IdealSheafData) [hI : Fact (genericPoint Y ∉ I.support)] :
    Fact (genericPoint X ∉ (I.comap f).support) :=
  ⟨genericPoint_not_mem_comap_support f I hI.out⟩

/-- The global map of Rees blow-ups of a finite dominant morphism of
integral schemes is dominant. -/
theorem globalReesMap_isDominant (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (I : Y.IdealSheafData) (hI : genericPoint Y ∉ I.support) :
    IsDominant (globalReesMap f I) := by
  obtain ⟨U₀, hU₀, hgU₀, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  let A₀ : Y.affineOpens := ⟨U₀, hU₀⟩
  have hA₀ : (A₀.1 : Set Y).Nonempty := ⟨_, hgU₀⟩
  haveI : Nonempty A₀.1 := hA₀.to_subtype
  have hgX : genericPoint X ∈ (preimageAffine f A₀).1 := by
    change f (genericPoint X) ∈ A₀.1
    rw [map_genericPoint_eq_of_isDominant f]
    exact hgU₀
  haveI : Nonempty (preimageAffine f A₀).1 := ⟨⟨_, hgX⟩⟩
  obtain ⟨a, ha⟩ := exists_ne_zero_mem_ideal I hI A₀ hA₀
  have hinj : Function.Injective (f.app A₀.1).hom := by
    rw [Scheme.Hom.app_eq_appLE]
    exact Pcf.Bounding.appLE_injective_of_dominant f A₀.1 _ _
  haveI := reesProjMap_isDominant_of_injective (f.app A₀.1).hom hinj (I.ideal A₀) a ha
  haveI : IsDominant (liftReesMapApp f I A₀) := by
    change IsDominant (reesProjMap (f.app A₀.1).hom (I.ideal A₀))
    infer_instance
  letI := reesProj_isIntegral_of_nonempty I hI A₀ hA₀
  haveI := globalRees_irreducibleSpace I hI
  haveI : IsDominant (globalReesChart I A₀) :=
    ⟨(globalReesChart I A₀).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  haveI : IsDominant (globalReesChart (I.comap f) (preimageAffine f A₀) ≫ globalReesMap f I) := by
    rw [globalReesChart_globalReesMap]
    infer_instance
  exact IsDominant.of_comp (globalReesChart (I.comap f) (preimageAffine f A₀)) _

end Integral

section Birational

variable {Y : Scheme.{u}}

/-- A dominant morphism of integral schemes inducing an isomorphism of
generic stalks induces a surjective map of function fields. -/
theorem schemeGenericFieldHom_surjective_of_isIso {X Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] (φ : Z ⟶ X) [IsDominant φ] [IsIso (φ.stalkMap (genericPoint Z))] :
    Function.Surjective (Pcf.schemeGenericFieldHom φ) := by
  let hgp := map_genericPoint_eq_of_isDominant φ
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  rw [Pcf.schemeGenericFieldHom_eq_stalkCongr]
  exact ((ConcreteCategory.bijective_of_isIso
    (φ.stalkMap (genericPoint Z))).surjective).comp e.symm.surjective

/-- The global Rees blow-up is separated over a locally Noetherian base. -/
theorem globalReesToBase_isSeparated [IsLocallyNoetherian Y] (I : Y.IdealSheafData) :
    IsSeparated (globalReesToBase I) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsSeparated) Y.directedAffineCover]
  intro U
  have h := (globalReesChart_isPullback I U).flip
  haveI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have hfg : (I.ideal U).FG := IsNoetherian.noetherian _
  letI : IsProper (reesProjToSpec (I.ideal U)) := reesProjToSpec_isProper' _ hfg
  change IsSeparated (pullback.snd (globalReesToBase I) U.1.ι)
  rw [← h.isoPullback_inv_snd]
  dsimp only [affineReesToOpen]
  infer_instance

variable [IsIntegral Y]


/-- The global Rees blow-up is birational: it induces a surjection, hence an
isomorphism, of function fields. -/
theorem globalReesToBase_genericField_surjective (I : Y.IdealSheafData)
    (hI : genericPoint Y ∉ I.support) :
    letI := globalRees_isIntegral I hI
    letI := globalReesToBase_isDominant I hI
    Function.Surjective (Pcf.schemeGenericFieldHom (globalReesToBase I)) := by
  letI := globalRees_isIntegral I hI
  letI := globalReesToBase_isDominant I hI
  obtain ⟨U₀, hU₀, hgU₀, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  let A₀ : Y.affineOpens := ⟨U₀, hU₀⟩
  have hA₀ : (A₀.1 : Set Y).Nonempty := ⟨_, hgU₀⟩
  haveI : Nonempty A₀.1 := hA₀.to_subtype
  obtain ⟨a, ha⟩ := exists_ne_zero_mem_ideal I hI A₀ hA₀
  letI : IsIntegral (reesProj (I.ideal A₀)) := reesProj_isIntegral (I.ideal A₀) a ha
  haveI : IsDominant (reesProjToSpec (I.ideal A₀)) := reesProjToSpec_isDominant (I.ideal A₀) a ha
  haveI : IsIso ((reesProjToSpec (I.ideal A₀)).stalkMap (genericPoint (reesProj (I.ideal A₀)))) :=
    reesProjToSpec_genericStalk_isIso (I.ideal A₀) a ha
  haveI : Nonempty (Spec Γ(Y, A₀.1)) := ⟨A₀.2.isoSpec.hom ⟨_, hgU₀⟩⟩
  haveI : IsDominant A₀.2.fromSpec :=
    ⟨A₀.2.fromSpec.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  haveI : IsDominant (globalReesChart I A₀) :=
    ⟨(globalReesChart I A₀).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hcomp := Pcf.schemeGenericFieldHom_congr (globalReesChart_toBase' I A₀)
  rw [Pcf.schemeGenericFieldHom_comp, Pcf.schemeGenericFieldHom_comp] at hcomp
  have hsurj : Function.Surjective ((Pcf.schemeGenericFieldHom (reesProjToSpec (I.ideal A₀))).comp
      (Pcf.schemeGenericFieldHom A₀.2.fromSpec)) :=
    (schemeGenericFieldHom_surjective_of_isIso (reesProjToSpec (I.ideal A₀))).comp
      (schemeGenericFieldHom_surjective_of_isIso A₀.2.fromSpec)
  intro y
  obtain ⟨z, hz⟩ := hsurj (Pcf.schemeGenericFieldHom (globalReesChart I A₀) y)
  refine ⟨z, (Pcf.schemeGenericFieldHom (globalReesChart I A₀)).injective ?_⟩
  calc Pcf.schemeGenericFieldHom (globalReesChart I A₀)
        (Pcf.schemeGenericFieldHom (globalReesToBase I) z)
      = ((Pcf.schemeGenericFieldHom (globalReesChart I A₀)).comp
          (Pcf.schemeGenericFieldHom (globalReesToBase I))) z := rfl
    _ = _ := by rw [hcomp]
    _ = _ := hz

end Birational

section Normalized

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f]
  [IsDominant f] (I : Y.IdealSheafData) [hI : Fact (genericPoint Y ∉ I.support)]

instance globalReesMap_isDominant_of_fact : IsDominant (globalReesMap f I) :=
  globalReesMap_isDominant f I hI.out

/-- The normalized blow-up `f' : X' ⟶ Y'` of `f` along the centre `I`, as in
`latex/paper-p.tex`, Definition `defn:normalized-blow-up`: the lift of the
global map of Rees blow-ups to the absolute normalizations. Here
`X' = globalNormalizedBlowup (I.comap f)` is the normalization of the blow-up
of `X` along the scheme-theoretic inverse image of the centre.

`paper-p.tex` correspondence: Proposition 7.7 (`prop:normalized-blowup-construction`), Definition
7.8 (`defn:normalized-blow-up`). -/
def globalNormalizedBlowupMap :
    globalNormalizedBlowup (I.comap f) ⟶ globalNormalizedBlowup I :=
  Pcf.schemeDominantNormalizationMorphism (globalReesMap f I)

/-- The normalized blow-up square `β ∘ f' = f ∘ α`. -/
@[reassoc]
theorem globalNormalizedBlowupMap_comm :
    globalNormalizedBlowupMap f I ≫ globalNormalizedBlowupToBase I =
      globalNormalizedBlowupToBase (I.comap f) ≫ f := by
  rw [globalNormalizedBlowupMap, globalNormalizedBlowupToBase,
    Pcf.schemeDominantNormalizationMorphism_comp_normalizationMap_assoc, globalReesMap_toBase,
    globalNormalizedBlowupToBase, Category.assoc]

instance globalNormalizedBlowupMap_isDominant : IsDominant (globalNormalizedBlowupMap f I) := by
  dsimp only [globalNormalizedBlowupMap]
  infer_instance

/-- Over a field, the normalized blow-up is finite. -/
theorem globalNormalizedBlowupMap_isFinite (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] : IsFinite (globalNormalizedBlowupMap f I) := by
  haveI : LocallyOfFiniteType (f ≫ s) := inferInstance
  haveI := globalRees_normalizationMap_isFinite (I.comap f) k (f ≫ s)
  have : IsFinite (globalNormalizedBlowupMap f I ≫ Palomar.normalizationMap (globalRees I)) := by
    rw [globalNormalizedBlowupMap, Pcf.schemeDominantNormalizationMorphism_comp_normalizationMap]
    infer_instance
  exact IsFinite.of_comp _ (Palomar.normalizationMap (globalRees I))

/-- Over a field, the normalized blow-up is surjective. -/
theorem globalNormalizedBlowupMap_surjective (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] : Function.Surjective (globalNormalizedBlowupMap f I) := by
  haveI := globalNormalizedBlowupMap_isFinite f I k s
  exact (surjective_of_isDominant_of_isClosed_range (globalNormalizedBlowupMap f I)
    (globalNormalizedBlowupMap f I).isClosedMap.isClosed_range).surj

/-- Uniqueness: any dominant morphism `X' ⟶ Y'` making the normalized
blow-up square commute is the normalized blow-up. -/
theorem globalNormalizedBlowupMap_unique (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] (F : globalNormalizedBlowup (I.comap f) ⟶ globalNormalizedBlowup I)
    [IsDominant F]
    (hF : F ≫ globalNormalizedBlowupToBase I = globalNormalizedBlowupToBase (I.comap f) ≫ f) :
    F = globalNormalizedBlowupMap f I := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  haveI := globalReesToBase_isSeparated I
  haveI := globalReesToBase_isDominant I hI.out
  haveI : IsSeparated (globalNormalizedBlowupToBase I) := by
    dsimp only [globalNormalizedBlowupToBase]
    infer_instance
  apply dominantLift_eq_of_genericField_surjective (globalNormalizedBlowupToBase I) ?_ F
    (globalNormalizedBlowupMap f I) (hF.trans (globalNormalizedBlowupMap_comm f I).symm)
  have h' := Pcf.schemeGenericFieldHom_congr (φ := globalNormalizedBlowupToBase I)
    (ψ := Palomar.normalizationMap (globalRees I) ≫ globalReesToBase I) rfl
  rw [h', Pcf.schemeGenericFieldHom_comp]
  exact (schemeGenericFieldHom_surjective_of_isIso
    (Palomar.normalizationMap (globalRees I))).comp
    (globalReesToBase_genericField_surjective I hI.out)

/-- `latex/paper-p.tex`, Proposition `prop:normalized-blowup-construction`, for
the global normalized blow-ups: there is a unique finite surjective morphism
`f' : X' ⟶ Y'` with `β ∘ f' = f ∘ α`.

`paper-p.tex` correspondence: Proposition 7.7 (`prop:normalized-blowup-construction`). -/
theorem globalNormalizedBlowupMap_existsUnique_finiteSurjective (k : Type u) [Field k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] :
    ∃! F : globalNormalizedBlowup (I.comap f) ⟶ globalNormalizedBlowup I,
      IsFinite F ∧ Function.Surjective F ∧
        F ≫ globalNormalizedBlowupToBase I = globalNormalizedBlowupToBase (I.comap f) ≫ f := by
  refine ⟨globalNormalizedBlowupMap f I, ⟨globalNormalizedBlowupMap_isFinite f I k s,
    globalNormalizedBlowupMap_surjective f I k s, globalNormalizedBlowupMap_comm f I⟩, ?_⟩
  rintro F ⟨-, hFs, hF⟩
  haveI : Surjective F := ⟨hFs⟩
  exact globalNormalizedBlowupMap_unique f I k s F hF

end Normalized

#print axioms globalReesMap_isDominant
#print axioms globalReesToBase_genericField_surjective
#print axioms globalNormalizedBlowupMap_existsUnique_finiteSurjective

end
end Pcf.Bounding.AllCodimBlowup
