/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPDegreeDisplays
public import Pcf.Bounding.NormalSchemePCFComparison
public import Pcf.Bounding.SchemeFiniteResidueDelta
public import Pcf.Stacks.Purity.NormalizationTower
public import Pcf.Bounding.AllCodimCoreGood

/-!
# Identifying the source's `ρ` in display l. 1969

In `lem:pcf-transfer-charp` the map `ρ : Y' → M` is finite, `Y'` and `M` are
normal, and `k(Y')/k(M)` is purely inseparable. This file proves that `Y'` is
the normalization of `M` in `E = k(Y')`, by an isomorphism over `M`, and
transports display l. 1969 from the normalization model
(`paperP_transfer_purelyInseparable_degree_display`) to `ρ` itself.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Relative normalization along a factorization `h = f ≫ g` with `g`
integral and `f.fromNormalization` an isomorphism is an isomorphism. -/
theorem normalizationDesc_isIso_of_factor'
    {X Y Z : Scheme.{u}} (h : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom g]
    [QuasiCompact h] [QuasiSeparated h] [IsIso f.fromNormalization]
    (H : h = f ≫ g) : IsIso (h.normalizationDesc f g H) := by
  subst H
  exact Pcf.Stacks.normalizationDesc_isIso_of_fromNormalization_isIso f g

/-- The model map `Spec k(Y') → M` of the normalization of `M` in `k(Y')`
factors through the generic point of `Y'` and `ρ`. -/
theorem schemeFieldExtensionInclusion_eq_genericInclusion_comp
    {M Y' : Scheme.{u}} [IsIntegral M] [IsIntegral Y'] (ρ : Y' ⟶ M) [IsDominant ρ] :
    letI := (schemeGenericFieldHom ρ).toAlgebra
    schemeFieldExtensionInclusion M Y'.functionField =
      schemeGenericInclusion Y' ≫ ρ := by
  letI := (schemeGenericFieldHom ρ).toAlgebra
  rw [← schemeGenericMorphism_comp]
  unfold schemeFieldExtensionInclusion
  congr 1
  change Spec.map (Spec.preimage (schemeGenericMorphism ρ)) = _
  exact Spec.map_preimage _

/-- A normal integral `Y'` finite over `M` is the normalization of `M` in its
function field: the universal map from the relative normalization of
`Spec k(Y') → M` to `Y'` is an isomorphism over `M`. -/
theorem normal_finite_isIso_normalizationDesc
    {M Y' : Scheme.{u}} [IsIntegral M] [IsIntegral Y'] [IsNormalScheme Y']
    (ρ : Y' ⟶ M) [IsFinite ρ] [IsDominant ρ] :
    letI := (schemeGenericFieldHom ρ).toAlgebra
    ∃ H : schemeFieldExtensionInclusion M Y'.functionField = schemeGenericInclusion Y' ≫ ρ,
      IsIso ((schemeFieldExtensionInclusion M Y'.functionField).normalizationDesc
          (schemeGenericInclusion Y') ρ H) ∧
        (schemeFieldExtensionInclusion M Y'.functionField).normalizationDesc
          (schemeGenericInclusion Y') ρ H ≫ ρ =
          (schemeFieldExtensionInclusion M Y'.functionField).fromNormalization := by
  letI := (schemeGenericFieldHom ρ).toAlgebra
  have H := schemeFieldExtensionInclusion_eq_genericInclusion_comp ρ
  haveI : IsIso (schemeGenericInclusion Y').fromNormalization :=
    normalScheme_normalizationMap_isIso Y'
  exact ⟨H, normalizationDesc_isIso_of_factor' _ _ ρ H, Scheme.Hom.normalizationDesc_comp _ _ _ H⟩

/-- Purity of a residue extension transports from `φ ≫ ρ` to `ρ` when `φ`
is an isomorphism. -/
theorem isPurelyInseparable_residueFieldMap_of_comp_iso
    {N Y' M : Scheme.{u}} (φ : N ⟶ Y') [IsIso φ] (ρ : Y' ⟶ M) (g : N ⟶ M)
    (hg : φ ≫ ρ = g) (x : N) (y : Y') (hy : φ x = y)
    (h : letI := (g.residueFieldMap x).hom.toAlgebra
      IsPurelyInseparable (M.residueField (g x)) (N.residueField x)) :
    letI := (ρ.residueFieldMap y).hom.toAlgebra
    IsPurelyInseparable (M.residueField (ρ y)) (Y'.residueField y) := by
  subst hg hy
  letI : Algebra (M.residueField (ρ (φ x))) (Y'.residueField (φ x)) :=
    (ρ.residueFieldMap (φ x)).hom.toAlgebra
  letI : Algebra (Y'.residueField (φ x)) (N.residueField x) :=
    (φ.residueFieldMap x).hom.toAlgebra
  letI : Algebra (M.residueField (ρ (φ x))) (N.residueField x) :=
    ((φ ≫ ρ).residueFieldMap x).hom.toAlgebra
  letI : IsScalarTower (M.residueField (ρ (φ x))) (Y'.residueField (φ x))
      (N.residueField x) := IsScalarTower.of_algebraMap_eq' (by
    change ((φ ≫ ρ).residueFieldMap x).hom = _
    rw [Scheme.residueFieldMap_comp]
    rfl)
  letI : IsPurelyInseparable (M.residueField (ρ (φ x))) (N.residueField x) := h
  exact IsPurelyInseparable.tower_bot (M.residueField (ρ (φ x))) (Y'.residueField (φ x))
    (N.residueField x)

/-- **Display l. 1969 for the source's `ρ`.** Let `ρ : Y' → M` be a finite
dominant morphism of normal integral locally Noetherian schemes over a field
`k` of exponential characteristic `p`, with `k(Y')/k(M)` purely inseparable,
and put `q = [k(Y') : k(M)]`. Then `Y'` is the normalization of `M` in `k(Y')`
(an isomorphism over `M`, see the proof), and for every integral effective
divisor `D` of `Y'`, with `D_M = ρ(D)`: `κ(D)/κ(D_M)` is purely inseparable,
`q = e(D/D_M)[κ(D):κ(D_M)]`, and `δ_ρ(D) = q`. -/
theorem paperP_transfer_rho_degree_display
    (k : Type u) [Field k] (pchar : ℕ) [ExpChar k pchar]
    {M Y' : Scheme.{u}} [IsIntegral M] [IsIntegral Y']
    [IsLocallyNoetherian M] [IsLocallyNoetherian Y'] [IsNormalScheme M] [IsNormalScheme Y']
    (s : M ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (ρ : Y' ⟶ M) [IsFinite ρ] [IsDominant ρ]
    (hpure : letI := (schemeGenericFieldHom ρ).toAlgebra
      IsPurelyInseparable M.functionField Y'.functionField)
    (D : SchemeDivisorPoint Y') :
    letI := (schemeGenericFieldHom ρ).toAlgebra
    letI := (ρ.residueFieldMap D.1).hom.toAlgebra
    IsPurelyInseparable (M.residueField (ρ D.1)) (Y'.residueField D.1) ∧
      Module.finrank M.functionField Y'.functionField =
        schemeDivisorRamificationIdx ρ D *
          Module.finrank (M.residueField (ρ D.1)) (Y'.residueField D.1) ∧
      schemeDivisorDelta ρ D = Module.finrank M.functionField Y'.functionField := by
  letI : Algebra M.functionField Y'.functionField := (schemeGenericFieldHom ρ).toAlgebra
  letI : IsPurelyInseparable M.functionField Y'.functionField := hpure
  letI : FiniteDimensional M.functionField Y'.functionField := schemeGenericFieldHom_finite ρ
  let m := schemeFieldExtensionInclusion M Y'.functionField
  let f := schemeGenericInclusion Y'
  have H : m = f ≫ ρ := schemeFieldExtensionInclusion_eq_genericInclusion_comp ρ
  haveI : IsIso f.fromNormalization := normalScheme_normalizationMap_isIso Y'
  let φ := m.normalizationDesc f ρ H
  haveI : IsIso φ := normalizationDesc_isIso_of_factor' m f ρ H
  have hφρ : φ ≫ ρ = m.fromNormalization := m.normalizationDesc_comp f ρ H
  haveI : IsFinite m.fromNormalization := by rw [← hφρ]; infer_instance
  haveI : IsDominant m.fromNormalization := by rw [← hφρ]; infer_instance
  let t : m.normalization ⟶ Spec (.of k) := m.fromNormalization ≫ s
  let D' : SchemeDivisorPoint m.normalization :=
    ⟨(inv φ) D.1, coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k t (inv φ) D⟩
  have hφD : φ D'.1 = D.1 := by
    change (inv φ ≫ φ) D.1 = D.1
    simp
  have hρD : m.fromNormalization D'.1 = ρ D.1 := by
    rw [← hφρ, Scheme.Hom.comp_apply, hφD]
  obtain ⟨V, hV, hDV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show ρ D.1 ∈ (⊤ : M.Opens) from trivial)
  let U : M.affineOpens := ⟨V, hV⟩
  haveI : Nonempty (U : M.Opens) := ⟨⟨ρ D.1, hDV⟩⟩
  have hd : D'.1 ∈ m.fromNormalization ⁻¹ᵁ (U : M.Opens) := by
    change m.fromNormalization D'.1 ∈ V
    rw [hρD]; exact hDV
  letI := schemeStalkAlgebraOfField k s (genericPoint M)
  haveI : ExpChar M.functionField pchar :=
    expChar_of_injective_ringHom (algebraMap k (M.presheaf.stalk (genericPoint M))).injective
      pchar
  letI := schemeAffineAlgebraOfField k s U
  haveI : ExpChar ((U.2.primeIdealOf ⟨m.fromNormalization D'.1, hd⟩).asIdeal).ResidueField
      pchar :=
    expChar_of_injective_ringHom
      ((algebraMap Γ(M, U) _).comp (algebraMap k Γ(M, U))).injective pchar
  obtain ⟨hpure', -, hδ'⟩ :=
    paperP_transfer_purelyInseparable_degree_display M Y'.functionField U D' hd pchar
  have hδφ : schemeDivisorDelta φ D' = 1 := by
    apply schemeDivisorDelta_eq_one_of_formallyEtale
    have hbij : Function.Bijective (φ.stalkMap D'.1).hom :=
      ConcreteCategory.bijective_of_isIso _
    rw [RingHom.FormallyEtale]
    letI := (φ.stalkMap D'.1).hom.toAlgebra
    exact Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij)
  have hmap : D'.mapFiniteDominantNormal φ = D := Subtype.ext hφD
  have hδ : schemeDivisorDelta ρ D = Module.finrank M.functionField Y'.functionField := by
    rw [← hδ', ← hφρ, schemeDivisorDelta_comp_of_isFinite φ ρ D', hδφ, mul_one, hmap]
  have hpureD : (letI := (ρ.residueFieldMap D.1).hom.toAlgebra
      IsPurelyInseparable (M.residueField (ρ D.1)) (Y'.residueField D.1)) :=
    isPurelyInseparable_residueFieldMap_of_comp_iso φ ρ m.fromNormalization hφρ D'.1 D.1 hφD
      hpure'
  letI := (ρ.residueFieldMap D.1).hom.toAlgebra
  refine ⟨hpureD, ?_, hδ⟩
  rw [← hδ]
  unfold schemeDivisorDelta
  rw [IsPurelyInseparable.finInsepDegree_eq]

#print axioms normalizationDesc_isIso_of_factor'
#print axioms paperP_transfer_rho_degree_display
#print axioms normal_finite_isIso_normalizationDesc

end

end Pcf
