/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NormalSchemePCFComparison
public import Pcf.Bounding.PaperPNormalizationLiftUnique
public import Pcf.Examples.PaperP.BirationalAffineNormalization

/-!
# A finite birational map from a normal integral scheme is the normalization

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): "Its normalization is `F`", i.e.
`ν : E ×ₖ ℙ¹ → X` is the normalization of `X`.

Let `ν : N → X` be a finite dominant morphism of integral schemes with `N` normal, birational in
the sense that the induced map of generic points `Spec K(N) → Spec K(X)`
(`schemeGenericMorphism ν`) is an isomorphism. Then

* **`normalizationIsoOfBirational ν : Palomar.normalization X ≅ N`**, over `X`
  (`normalizationIsoOfBirational_hom_comp`);
* `normalizationMap_isFinite_of_birational`: the normalization map of `X` is finite;
* `isIso_stalkMap_of_comp`: a convenient source of birationality (`ν` restricted along an open
  immersion `c` is an open immersion, at the image of a point of `c`'s source);
* `schemeGenericMorphism_isIso_of_stalkMap`: `IsIso (ν.stalkMap η_N)` gives birationality.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Pcf.Examples.PaperP.NormalizationOfBirationalCover

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

/-- The normalization of `Y` in `T` does not change when `T` is replaced by an isomorphic scheme:
if `h.fromNormalization` is an isomorphism, so is `(e ≫ h).fromNormalization`. -/
theorem fromNormalization_isIso_iso_comp {T T' Y : Scheme.{u}} (e : T ⟶ T') [IsIso e]
    (h : T' ⟶ Y) [QuasiCompact h] [QuasiSeparated h] [IsIso h.fromNormalization] :
    IsIso (e ≫ h).fromNormalization := by
  let f := e ≫ h
  let a : f.normalization ⟶ h.normalization :=
    f.normalizationDesc (e ≫ h.toNormalization) h.fromNormalization (by simp [f])
  let b : h.normalization ⟶ f.normalization :=
    h.normalizationDesc (inv e ≫ f.toNormalization) f.fromNormalization (by simp [f])
  have ha : a ≫ h.fromNormalization = f.fromNormalization := f.normalizationDesc_comp _ _ _
  have hb : b ≫ f.fromNormalization = h.fromNormalization := h.normalizationDesc_comp _ _ _
  have hab : a ≫ b = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
    · rw [← Category.assoc, f.toNormalization_normalizationDesc, Category.assoc,
        h.toNormalization_normalizationDesc, IsIso.hom_inv_id_assoc, Category.comp_id]
    · rw [Category.assoc, hb, ha]
    · simp
  refine ⟨⟨inv h.fromNormalization ≫ b, ?_, ?_⟩⟩
  · change f.fromNormalization ≫ _ = _
    rw [← ha, Category.assoc, IsIso.hom_inv_id_assoc, hab]
  · change (inv h.fromNormalization ≫ b) ≫ f.fromNormalization = _
    rw [Category.assoc, hb, IsIso.inv_hom_id]

variable {N X : Scheme.{u}} [IsIntegral N] [IsIntegral X] (ν : N ⟶ X) [IsFinite ν] [IsDominant ν]
  [IsIso (schemeGenericMorphism ν)]

/-- `Spec K(X) ≅ Spec K(N) → N`. -/
noncomputable abbrev genericLift : Spec X.functionField ⟶ N :=
  inv (schemeGenericMorphism ν) ≫ schemeGenericInclusion N

theorem genericLift_comp : schemeGenericInclusion X = genericLift ν ≫ ν := by
  rw [Category.assoc, ← schemeGenericMorphism_comp, IsIso.inv_hom_id_assoc]

/-- The comparison map `X̃ → N`, over `X`. -/
noncomputable def normalizationToCover : Palomar.normalization X ⟶ N :=
  (schemeGenericInclusion X).normalizationDesc (genericLift ν) ν (genericLift_comp ν)

@[reassoc (attr := simp)]
theorem normalizationToCover_comp :
    normalizationToCover ν ≫ ν = Palomar.normalizationMap X :=
  (schemeGenericInclusion X).normalizationDesc_comp _ _ _

theorem normalizationToCover_isIso [IsNormalScheme N] : IsIso (normalizationToCover ν) := by
  haveI : IsIso (schemeGenericInclusion N).fromNormalization :=
    normalScheme_normalizationMap_isIso N
  haveI : IsIso (genericLift ν).fromNormalization :=
    fromNormalization_isIso_iso_comp (inv (schemeGenericMorphism ν)) (schemeGenericInclusion N)
  exact BirationalAffineNormalization.normalizationDesc_isIso_of_factor _ _ _
    (genericLift_comp ν)

/-- **A finite birational map from a normal integral scheme is the normalization:**
`X̃ ≅ N` over `X`. -/
noncomputable def normalizationIsoOfBirational [IsNormalScheme N] :
    Palomar.normalization X ≅ N :=
  haveI := normalizationToCover_isIso ν
  asIso (normalizationToCover ν)

@[reassoc (attr := simp)]
theorem normalizationIsoOfBirational_hom_comp [IsNormalScheme N] :
    (normalizationIsoOfBirational ν).hom ≫ ν = Palomar.normalizationMap X :=
  normalizationToCover_comp ν

@[reassoc (attr := simp)]
theorem normalizationIsoOfBirational_inv_comp [IsNormalScheme N] :
    (normalizationIsoOfBirational ν).inv ≫ Palomar.normalizationMap X = ν := by
  rw [Iso.inv_comp_eq, normalizationIsoOfBirational_hom_comp]

include ν in
theorem normalizationMap_isFinite_of_birational [IsNormalScheme N] :
    IsFinite (Palomar.normalizationMap X) := by
  rw [← normalizationIsoOfBirational_hom_comp ν]
  infer_instance

end Pcf.Examples.PaperP.NormalizationOfBirationalCover

namespace Pcf.Examples.PaperP.NormalizationOfBirationalCover

set_option linter.style.haveILetI false

universe u

/-- If `c ≫ ν` is an open immersion for an open immersion `c`, then `ν` is an isomorphism on the
stalk at `c w`. -/
theorem isIso_stalkMap_of_comp {W N X : Scheme.{u}} (c : W ⟶ N) (ν : N ⟶ X) [IsOpenImmersion c]
    [IsOpenImmersion (c ≫ ν)] (w : W) : IsIso (ν.stalkMap (c w)) := by
  have h := Scheme.Hom.stalkMap_comp c ν w
  have h1 : IsIso ((c ≫ ν).stalkMap w) := inferInstance
  have : IsIso (c.stalkMap w) := inferInstance
  rw [h] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (ν.stalkMap (c w)) (c.stalkMap w) _ h1

/-- **Birationality from the generic stalk.** -/
theorem schemeGenericMorphism_isIso_of_stalkMap {N X : Scheme.{u}} [IsIntegral N] [IsIntegral X]
    (ν : N ⟶ X) [IsDominant ν] [IsIso (ν.stalkMap (genericPoint N))] :
    IsIso (schemeGenericMorphism ν) := by
  have key : ∀ {x y : X} (h : x = y),
      IsIso (X.presheaf.stalkSpecializes (specializes_of_eq h)) := by
    rintro x _ rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  haveI := key (map_genericPoint_eq_of_isDominant ν)
  unfold schemeGenericMorphism
  infer_instance

end Pcf.Examples.PaperP.NormalizationOfBirationalCover

#print axioms Pcf.Examples.PaperP.NormalizationOfBirationalCover.normalizationIsoOfBirational
#print axioms
  Pcf.Examples.PaperP.NormalizationOfBirationalCover.schemeGenericMorphism_isIso_of_stalkMap
#print axioms Pcf.Examples.PaperP.NormalizationOfBirationalCover.isIso_stalkMap_of_comp
