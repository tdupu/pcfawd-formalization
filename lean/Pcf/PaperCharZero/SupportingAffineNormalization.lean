/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationNormal
public import Pcf.Bounding.GlobalNormalizationMorphism
public import Pcf.PaperCharZero.SupportingTower
public import Pcf.Stacks.Abhyankar.Scheme.TameBridge
public import Pcf.Bounding.NormalSchemePCFComparison

/-!
# The canonical normalization of an affine integral scheme

For a domain `R` with fraction field `K`, the project's canonical normalization
`Palomar.normalization (Spec R)` is Mathlib's relative normalization of `Spec R`
in its generic point. This file identifies it with `Spec (integralClosure R K)`
over `Spec R`, using the actual affine chart of the relative normalization over
the open `⊤`.

As a transport lemma, a finite dominant morphism `g : Y ⟶ Spec R` from a
normal integral scheme which factors as an isomorphism `Y ≅ Palomar.normalization
(Spec R)` followed by the normalization map has an isomorphism as its canonical
normalized lift; its normalized branch support is therefore empty. This is the
step "`g` is the normalization of `B`, so its lift is the identity" used in
`paper.tex`, Example `ex:cusp`.
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

variable (R : CommRingCat.{u}) [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The open `⊤` of `Spec R`, as an affine open. -/
def specTopAffine : (Spec R).affineOpens := ⟨⊤, isAffineOpen_top _⟩

instance specTop_nonempty : Nonempty (⊤ : (Spec R).Opens) :=
  ⟨⟨genericPoint (Spec R), trivial⟩⟩

/-- The base ring of the top chart is `R`. -/
def specTopSectionsEquiv : Γ(Spec R, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- The actual function field of `Spec R` is the chosen fraction field. -/
def specFunctionFieldEquiv : (Spec R).functionField ≃+* K :=
  (IsLocalization.algEquiv (nonZeroDivisors R) (Spec R).functionField K).toRingEquiv

/-- The generic-point sections above `⊤` are the chosen fraction field. -/
def specGenericSectionsEquiv :
    Γ(Spec (Spec R).functionField, schemeGenericInclusion (Spec R) ⁻¹ᵁ ⊤) ≃+* K :=
  (schemeGenericInclusionSectionsIso (Spec R) ⊤).commRingCatIsoToRingEquiv.trans
    (specFunctionFieldEquiv R K)

set_option backward.isDefEq.respectTransparency false in
theorem specGenericSections_apply (x : Γ(Spec R, ⊤)) :
    (schemeGenericInclusionSectionsIso (Spec R) ⊤).hom
        ((schemeGenericInclusion (Spec R)).app ⊤ x) =
      algebraMap R (Spec R).functionField ((Scheme.ΓSpecIso R).hom x) := by
  have hU : schemeGenericInclusion (Spec R)
      (IsLocalRing.closedPoint (Spec R).functionField) ∈ (⊤ : (Spec R).Opens) := trivial
  have h := Scheme.germ_stalkClosedPointTo (f := schemeGenericInclusion (Spec R)) ⊤ hU
  rw [Scheme.stalkClosedPointTo_fromSpecStalk] at h
  have h2 := congrArg (fun φ => φ.hom x) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  refine h2.symm.trans ?_
  rw [TopCat.Presheaf.stalkCongr_hom, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]
  obtain ⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso R).inv y = x :=
    ⟨(Scheme.ΓSpecIso R).hom x, by simp⟩
  simp only [Iso.inv_hom_id_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The two identifications are compatible with the generic inclusion. -/
theorem specGenericSectionsEquiv_compat (x : Γ(Spec R, ⊤)) :
    specGenericSectionsEquiv R K ((schemeGenericInclusion (Spec R)).app ⊤ x) =
      algebraMap R K (specTopSectionsEquiv R x) := by
  change specFunctionFieldEquiv R K ((schemeGenericInclusionSectionsIso (Spec R) ⊤).hom
    ((schemeGenericInclusion (Spec R)).app ⊤ x)) = _
  rw [specGenericSections_apply]
  exact (IsLocalization.algEquiv (nonZeroDivisors R) (Spec R).functionField K).commutes _

/-- The affine chart of the canonical normalization over `⊤`, rewritten as the
integral closure of `R` in `K`. -/
def specIntegralClosureSectionsEquiv :
    letI := ((schemeGenericInclusion (Spec R)).app ⊤).hom.toAlgebra
    integralClosure Γ(Spec R, ⊤)
        Γ(Spec (Spec R).functionField, schemeGenericInclusion (Spec R) ⁻¹ᵁ ⊤) ≃+*
      integralClosure R K :=
  letI := ((schemeGenericInclusion (Spec R)).app ⊤).hom.toAlgebra
  Pcf.Stacks.SchemeLevel.integralClosureRingEquiv (specTopSectionsEquiv R)
    (specGenericSectionsEquiv R K) (specGenericSectionsEquiv_compat R K)

/-- The actual chart of the relative normalization over the affine open `⊤`. -/
abbrev specNormalizationChart :
    (schemeGenericInclusion (Spec R)).normalizationOpenCover.X (specTopAffine R) ⟶
      Palomar.normalization (Spec R) :=
  (schemeGenericInclusion (Spec R)).normalizationOpenCover.f (specTopAffine R)

instance specNormalizationChart_isIso : IsIso (specNormalizationChart R) := by
  have : IsOpenImmersion (specNormalizationChart R) :=
    (schemeGenericInclusion (Spec R)).normalizationOpenCover.map_prop (specTopAffine R)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [← (schemeGenericInclusion (Spec R)).fromNormalization_preimage (specTopAffine R)]
  rfl

end Pcf.PaperCharZero

namespace Pcf.PaperCharZero

variable (R : CommRingCat.{u}) [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- `Spec` of the integral closure of `R` in `K`, mapped to the actual top chart. -/
def specIntegralClosureToChart :
    Spec (.of (integralClosure R K)) ⟶
      (schemeGenericInclusion (Spec R)).normalizationOpenCover.X (specTopAffine R) :=
  Spec.map (CommRingCat.ofHom (specIntegralClosureSectionsEquiv R K).toRingHom)

instance : IsIso (specIntegralClosureToChart R K) :=
  (Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso (specIntegralClosureSectionsEquiv R K)).op).isIso_hom

/-- **Task.** The canonical normalization of `Spec R` is `Spec` of the integral
closure of `R` in its fraction field. -/
def affineNormalizationIso :
    Spec (.of (integralClosure R K)) ≅ Palomar.normalization (Spec R) :=
  asIso (specIntegralClosureToChart R K ≫ specNormalizationChart R)

set_option backward.isDefEq.respectTransparency false in
/-- The identification is over `Spec R`. -/
@[reassoc]
theorem affineNormalizationIso_hom_normalizationMap :
    (affineNormalizationIso R K).hom ≫ Palomar.normalizationMap (Spec R) =
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R K))) := by
  simp only [affineNormalizationIso, asIso_hom, Category.assoc]
  erw [(schemeGenericInclusion (Spec R)).ι_fromNormalization (specTopAffine R)]
  erw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rw [specIntegralClosureToChart, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (specGenericSectionsEquiv_compat R K _).trans (congrArg (algebraMap R K)
    ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.apply_symm_apply r))

/-- The inverse identification is also over `Spec R`. -/
@[reassoc]
theorem affineNormalizationIso_inv_SpecMap :
    (affineNormalizationIso R K).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R K))) =
      Palomar.normalizationMap (Spec R) := by
  rw [← affineNormalizationIso_hom_normalizationMap, Iso.inv_hom_id_assoc]

/-- Two ring maps out of an integral closure agree once they agree on the base,
provided the common restriction to the base is injective. -/
theorem integralClosure_ringHom_ext {F : Type u} [CommRing F] [IsDomain F]
    (φ₁ φ₂ : integralClosure R K →+* F)
    (h : φ₁.comp (algebraMap R (integralClosure R K)) =
      φ₂.comp (algebraMap R (integralClosure R K)))
    (hinj : Function.Injective (φ₁.comp (algebraMap R (integralClosure R K)))) :
    φ₁ = φ₂ := by
  ext c
  obtain ⟨⟨a, s⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors R) (c : K)
  have hc' : c * algebraMap R (integralClosure R K) s = algebraMap R (integralClosure R K) a :=
    Subtype.ext hc
  have h₁ := congrArg φ₁ hc'
  have h₂ := congrArg φ₂ hc'
  rw [map_mul] at h₁ h₂
  have ha := congrArg (fun f : R →+* F => f a) h
  have hs := congrArg (fun f : R →+* F => f s) h
  simp only [RingHom.comp_apply] at ha hs
  have hs0 : φ₁ (algebraMap R (integralClosure R K) s) ≠ 0 := by
    intro h0
    have : (s : R) = 0 := hinj (by simpa only [RingHom.comp_apply, map_zero] using h0)
    exact nonZeroDivisors.coe_ne_zero s this
  apply mul_right_cancel₀ hs0
  rw [h₁, ha, ← h₂, hs]

set_option backward.isDefEq.respectTransparency false in
/-- Maps from the spectrum of a field into the canonical normalization of
`Spec R` are determined by their composite to `Spec R`, when that composite
hits the generic point. -/
theorem specNormalization_hom_ext_of_field {F : Type u} [Field F]
    (a₁ a₂ : Spec (.of F) ⟶ Palomar.normalization (Spec R))
    (h : a₁ ≫ Palomar.normalizationMap (Spec R) = a₂ ≫ Palomar.normalizationMap (Spec R))
    (hgen : (a₁ ≫ Palomar.normalizationMap (Spec R)) (IsLocalRing.closedPoint F) =
      genericPoint (Spec R)) :
    a₁ = a₂ := by
  let K := FractionRing R
  let e := affineNormalizationIso R K
  let φ₁ := Spec.preimage (a₁ ≫ e.inv)
  let φ₂ := Spec.preimage (a₂ ≫ e.inv)
  let α : R ⟶ CommRingCat.of (integralClosure R K) :=
    CommRingCat.ofHom (algebraMap R (integralClosure R K))
  have hφ (a : Spec (.of F) ⟶ Palomar.normalization (Spec R)) :
      Spec.map (α ≫ Spec.preimage (a ≫ e.inv)) = a ≫ Palomar.normalizationMap (Spec R) := by
    rw [Spec.map_comp, Spec.map_preimage, Category.assoc, affineNormalizationIso_inv_SpecMap]
  have hcomp : α ≫ φ₁ = α ≫ φ₂ := Spec.map_injective ((hφ a₁).trans (h.trans (hφ a₂).symm))
  have hinj : Function.Injective (φ₁.hom.comp (algebraMap R (integralClosure R K))) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    have hpt := hgen
    rw [← hφ a₁, genericPoint_eq_bot_of_affine] at hpt
    have hpt' := congrArg PrimeSpectrum.asIdeal hpt
    change Ideal.comap (α ≫ φ₁).hom (IsLocalRing.maximalIdeal F) = ⊥ at hpt'
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot] at hpt'
    exact hpt'
  have hring : φ₁ = φ₂ := by
    apply CommRingCat.hom_ext
    exact integralClosure_ringHom_ext R K φ₁.hom φ₂.hom (congrArg CommRingCat.Hom.hom hcomp) hinj
  have : a₁ ≫ e.inv = a₂ ≫ e.inv := by
    rw [← Spec.map_preimage (a₁ ≫ e.inv), ← Spec.map_preimage (a₂ ≫ e.inv)]
    exact congrArg Spec.map hring
  exact (cancel_mono e.inv).mp this

/-- **Transport.** If a finite dominant morphism `g : Y ⟶ Spec R` from a normal
integral scheme factors through the canonical normalization as `ψ ≫ ν`, then
the canonical normalized lift of `g` is `ν_Y ≫ ψ`. -/
theorem schemeGlobalNormalizationMorphism_eq_of_factor
    {Y : Scheme.{u}} [IsIntegral Y] [IsNormalScheme Y]
    (g : Y ⟶ Spec R) [IsFinite g] [IsDominant g]
    (ψ : Y ⟶ Palomar.normalization (Spec R))
    (hψ : ψ ≫ Palomar.normalizationMap (Spec R) = g) :
    schemeGlobalNormalizationMorphism g = Palomar.normalizationMap Y ≫ ψ := by
  symm
  apply schemeGlobalNormalizationMorphism_unique
  · rw [Category.assoc, hψ]
  · apply specNormalization_hom_ext_of_field R
    · simp only [Category.assoc, hψ, Scheme.Hom.toNormalization_fromNormalization_assoc,
        schemeGenericToNormalization_comp]
      exact (schemeGenericMorphism_comp g).symm
    · simp only [Category.assoc, hψ, Scheme.Hom.toNormalization_fromNormalization_assoc]
      change g ((Y.fromSpecStalk (genericPoint Y))
        (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)))) = _
      rw [Scheme.fromSpecStalk_closedPoint]
      exact map_genericPoint_eq_of_isDominant g

/-- The normalized lift in the factorization is an isomorphism when `ψ` is. -/
theorem schemeGlobalNormalizationMorphism_isIso_of_factor
    {Y : Scheme.{u}} [IsIntegral Y] [IsNormalScheme Y]
    (g : Y ⟶ Spec R) [IsFinite g] [IsDominant g]
    (ψ : Y ⟶ Palomar.normalization (Spec R)) [IsIso ψ]
    (hψ : ψ ≫ Palomar.normalizationMap (Spec R) = g) :
    IsIso (schemeGlobalNormalizationMorphism g) := by
  let : IsIso (Palomar.normalizationMap Y) := normalScheme_normalizationMap_isIso Y
  rw [schemeGlobalNormalizationMorphism_eq_of_factor R g ψ hψ]
  infer_instance

/-- An isomorphism has empty actual codimension-one reduced-fiber branch set. -/
theorem reducedFiberBranch_empty_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    schemeReducedFiberBranch f = ∅ := by
  ext E
  simp only [schemeReducedFiberBranch, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_not]
  let : IsIso (f.fiberToSpecResidueField E.1) :=
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField E.1)).isIso_snd_of_isIso
  exact isReduced_of_isOpenImmersion (f.fiberToSpecResidueField E.1)

/-- **Transport of normalized branch loci.** A morphism which factors as an
isomorphism onto the canonical normalization of `Spec R` followed by the
normalization map has empty normalized branch support. -/
theorem normalizedMorphismBranchSupport_empty_of_factor
    {Y : Scheme.{u}} [IsIntegral Y] [IsNormalScheme Y]
    (g : Y ⟶ Spec R) [IsFinite g] [IsDominant g]
    (ψ : Y ⟶ Palomar.normalization (Spec R)) [IsIso ψ]
    (hψ : ψ ≫ Palomar.normalizationMap (Spec R) = g) :
    normalizedMorphismBranchSupport g = ∅ := by
  let := schemeGlobalNormalizationMorphism_isIso_of_factor R g ψ hψ
  simp [normalizedMorphismBranchSupport, reducedFiberBranch_empty_of_isIso, divisorSupport]

end Pcf.PaperCharZero

#print axioms Pcf.PaperCharZero.specGenericSections_apply
#print axioms Pcf.PaperCharZero.specGenericSectionsEquiv_compat
#print axioms Pcf.PaperCharZero.specIntegralClosureSectionsEquiv
#print axioms Pcf.PaperCharZero.specNormalizationChart_isIso
#print axioms Pcf.PaperCharZero.affineNormalizationIso
#print axioms Pcf.PaperCharZero.affineNormalizationIso_hom_normalizationMap
#print axioms Pcf.PaperCharZero.affineNormalizationIso_inv_SpecMap
#print axioms Pcf.PaperCharZero.integralClosure_ringHom_ext
#print axioms Pcf.PaperCharZero.specNormalization_hom_ext_of_field
#print axioms Pcf.PaperCharZero.schemeGlobalNormalizationMorphism_eq_of_factor
#print axioms Pcf.PaperCharZero.schemeGlobalNormalizationMorphism_isIso_of_factor
#print axioms Pcf.PaperCharZero.reducedFiberBranch_empty_of_isIso
#print axioms Pcf.PaperCharZero.normalizedMorphismBranchSupport_empty_of_factor
