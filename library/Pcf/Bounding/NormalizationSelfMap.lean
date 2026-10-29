/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Self-maps of relative normalizations

Let `j : S ⟶ X` be quasi-compact and quasi-separated, and let `f : X ⟶ X`
and `φ : S ⟶ S` satisfy `φ ≫ j = j ≫ f`. The universal property of relative
normalization gives a unique self-map of `j.normalization` lying over `f` and
extending `φ`. This is the global intermediate-normalization map `h_M` of
`latex/paper-p.tex`, Lemma `lem:pcf-transfer-charp`, constructed without
gluing affine charts.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {S X : Scheme.{u}} (j : S ⟶ X) [QuasiCompact j] [QuasiSeparated j]

set_option backward.isDefEq.respectTransparency.types false in
/-- Two maps out of a relative normalization agree if they agree on the
source of `j` and lie over the same map through an affine morphism. -/
theorem normalization_hom_ext_over {T Z : Scheme.{u}} (a b : j.normalization ⟶ T)
    (c : T ⟶ Z) [IsAffineHom c] (e : X ⟶ Z)
    (ha : a ≫ c = j.fromNormalization ≫ e) (hb : b ≫ c = j.fromNormalization ≫ e)
    (hab : j.toNormalization ≫ a = j.toNormalization ≫ b) : a = b := by
  letI : IsAffineHom (pullback.snd c e) := MorphismProperty.pullback_snd _ _ ‹_›
  have hl := Scheme.Hom.normalization.hom_ext j (pullback.lift a j.fromNormalization ha)
    (pullback.lift b j.fromNormalization hb) (pullback.snd c e)
    (by
      apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.lift_fst] using hab
      · simp only [Category.assoc, pullback.lift_snd])
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
  simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst c e) hl

variable (f : X ⟶ X) (φ : S ⟶ S) (hφ : φ ≫ j = j ≫ f)

/-- The self-map of a relative normalization over `f` extending `φ`. -/
def normalizationSelfMap : j.normalization ⟶ j.normalization :=
  j.normalizationDesc
      (pullback.lift (φ ≫ j.toNormalization) j (by
        rw [Category.assoc, j.toNormalization_fromNormalization, hφ]))
      (pullback.snd j.fromNormalization f) (by rw [pullback.lift_snd]) ≫
    pullback.fst j.fromNormalization f

@[reassoc]
theorem normalizationSelfMap_fromNormalization :
    normalizationSelfMap j f φ hφ ≫ j.fromNormalization = j.fromNormalization ≫ f := by
  rw [normalizationSelfMap, Category.assoc, pullback.condition,
    ← Category.assoc, j.normalizationDesc_comp]

@[reassoc]
theorem toNormalization_normalizationSelfMap :
    j.toNormalization ≫ normalizationSelfMap j f φ hφ = φ ≫ j.toNormalization := by
  rw [normalizationSelfMap, ← Category.assoc, j.toNormalization_normalizationDesc,
    pullback.lift_fst]

/-- Uniqueness of the induced self-map. -/
theorem normalizationSelfMap_unique (h : j.normalization ⟶ j.normalization)
    (h₁ : h ≫ j.fromNormalization = j.fromNormalization ≫ f)
    (h₂ : j.toNormalization ≫ h = φ ≫ j.toNormalization) :
    h = normalizationSelfMap j f φ hφ :=
  normalization_hom_ext_over j _ _ j.fromNormalization f h₁
    (normalizationSelfMap_fromNormalization j f φ hφ)
    (h₂.trans (toNormalization_normalizationSelfMap j f φ hφ).symm)

instance normalizationSelfMap_isIntegralHom [IsIntegralHom f] :
    IsIntegralHom (normalizationSelfMap j f φ hφ) := by
  rw [normalizationSelfMap]
  infer_instance

/-- The induced self-map is finite when `f` and the normalization map are. -/
theorem normalizationSelfMap_isFinite [IsFinite f] [IsFinite j.fromNormalization] :
    IsFinite (normalizationSelfMap j f φ hφ) := by
  refine (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, ?_⟩
  have : LocallyOfFiniteType (normalizationSelfMap j f φ hφ ≫ j.fromNormalization) := by
    rw [normalizationSelfMap_fromNormalization]
    infer_instance
  exact locallyOfFiniteType_of_comp _ j.fromNormalization

/-- The induced self-map is dominant when `φ` is. -/
theorem normalizationSelfMap_isDominant [IsDominant φ] :
    IsDominant (normalizationSelfMap j f φ hφ) := by
  have : IsDominant (j.toNormalization ≫ normalizationSelfMap j f φ hφ) := by
    rw [toNormalization_normalizationSelfMap]
    infer_instance
  exact IsDominant.of_comp j.toNormalization _

#print axioms normalization_hom_ext_over
#print axioms normalizationSelfMap_fromNormalization
#print axioms toNormalization_normalizationSelfMap
#print axioms normalizationSelfMap_unique
#print axioms normalizationSelfMap_isFinite
#print axioms normalizationSelfMap_isDominant

end
end Pcf
