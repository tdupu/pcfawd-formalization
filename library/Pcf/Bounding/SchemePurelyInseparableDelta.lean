/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FieldExtensionNormalizationFieldEquiv
public import Pcf.Bounding.SchemePrimaryNormalizationDeltaDegree
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian
public import Pcf.Bounding.NormalSchemePCFComparison
public import Pcf.Stacks.Purity.Tag0BM9

/-!
# Constant local degree of a purely inseparable finite map

Let `ρ : Y ⟶ M` be finite and dominant between normal integral locally
Noetherian schemes over a field, with `k(Y) / k(M)` purely inseparable.
Then `δ_ρ(D) = [k(Y) : k(M)]` for every prime divisor `D` of `Y`. This is the
identity `δ_ρ(D) = q` in `latex/paper-p.tex`, Lemma
`lem:pcf-transfer-charp`. The proof identifies `Y` with the normalization of
`M` in `k(Y)` and applies the checked degree formula for that normalization.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- An isomorphism has local degree one at every divisor. -/
theorem schemeDivisorDelta_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X) : schemeDivisorDelta e d = 1 := by
  rw [schemeDivisorDelta_eq_one_iff_formallyEtale]
  have hbij : Function.Bijective (e.stalkMap d.1).hom :=
    ConcreteCategory.bijective_of_isIso (e.stalkMap d.1)
  letI := (e.stalkMap d.1).hom.toAlgebra
  change Algebra.FormallyEtale _ _
  exact Algebra.FormallyEtale.of_equiv
    (AlgEquiv.ofBijective (Algebra.ofId (Y.presheaf.stalk (e d.1)) _) hbij)

/-- The generic-point morphism followed by `ρ` is the field-extension
inclusion for the rational pullback along `ρ`. -/
theorem schemeGenericInclusion_comp_eq_fieldExtensionInclusion
    {M Y : Scheme.{u}} [IsIntegral M] [IsIntegral Y] (ρ : Y ⟶ M) [IsDominant ρ] :
    letI : Algebra M.functionField Y.functionField := (schemeGenericFieldHom ρ).toAlgebra
    schemeGenericInclusion Y ≫ ρ = schemeFieldExtensionInclusion M Y.functionField := by
  letI : Algebra M.functionField Y.functionField := (schemeGenericFieldHom ρ).toAlgebra
  rw [← schemeGenericMorphism_comp, schemeFieldExtensionInclusion]
  congr 1
  change schemeGenericMorphism ρ = Spec.map (Spec.preimage (schemeGenericMorphism ρ))
  rw [Spec.map_preimage]

/-- **Constant local degree of a purely inseparable comparison map.** -/
theorem schemeDivisorDelta_eq_finrank_of_purelyInseparable
    (k : Type u) [Field k]
    {M Y : Scheme.{u}} [IsIntegral M] [IsIntegral Y]
    [IsLocallyNoetherian M] [IsNormalScheme M]
    [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (s : M ⟶ Spec (.of k))
    (ρ : Y ⟶ M) [IsFinite ρ] [IsDominant ρ]
    (hpi : letI : Algebra M.functionField Y.functionField :=
        (schemeGenericFieldHom ρ).toAlgebra
      IsPurelyInseparable M.functionField Y.functionField)
    (d : SchemeDivisorPoint Y) :
    letI : Algebra M.functionField Y.functionField := (schemeGenericFieldHom ρ).toAlgebra
    schemeDivisorDelta ρ d = Module.finrank M.functionField Y.functionField := by
  letI : Algebra M.functionField Y.functionField := (schemeGenericFieldHom ρ).toAlgebra
  letI : IsPurelyInseparable M.functionField Y.functionField := hpi
  letI : FiniteDimensional M.functionField Y.functionField := schemeGenericFieldHom_finite ρ
  let jE := schemeFieldExtensionInclusion M Y.functionField
  have hjE : schemeGenericInclusion Y ≫ ρ = jE :=
    schemeGenericInclusion_comp_eq_fieldExtensionInclusion ρ
  haveI : IsIso (Palomar.normalizationMap Y) := normalScheme_normalizationMap_isIso Y
  let c₁ : jE.normalization ≅ (schemeGenericInclusion Y ≫ ρ).normalization :=
    Pcf.Stacks.normalizationIsoOfSourceIsoEq (schemeGenericInclusion Y ≫ ρ) (𝟙 _) jE
      (by rw [Category.id_comp, hjE])
  let c : jE.normalization ≅ Y :=
    c₁ ≪≫ asIso (schemeNormalizationMorphismComparison ρ) ≪≫
      asIso (Palomar.normalizationMap Y)
  have hc : c.hom ≫ ρ = jE.fromNormalization := by
    simp only [c, Iso.trans_hom, asIso_hom, Category.assoc,
      schemeNormalizationMorphismComparison_comp]
    exact Pcf.Stacks.normalizationIsoOfSourceIsoEq_hom_fromNormalization _ _ _ _
  have hρ : ρ = c.inv ≫ jE.fromNormalization := by
    rw [← hc, Iso.inv_hom_id_assoc]
  haveI : IsFinite jE.fromNormalization := by
    rw [← hc]
    infer_instance
  haveI : IsLocallyNoetherian jE.normalization :=
    isLocallyNoetherian_of_isOpenImmersion c.hom
  have h1 : schemeDivisorDelta ρ d =
      schemeDivisorDelta (c.inv ≫ jE.fromNormalization) d :=
    congrArg (fun φ => schemeDivisorDelta φ d) hρ
  rw [h1, schemeDivisorDelta_comp_of_isFinite c.inv jE.fromNormalization d,
    schemeDivisorDelta_of_isIso c.inv d, mul_one]
  let d' := d.mapFiniteDominantNormal c.inv
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show jE.fromNormalization d'.1 ∈ (⊤ : M.Opens) from trivial)
  let U' : M.affineOpens := ⟨U, hU⟩
  haveI : Nonempty (U' : M.Opens) := ⟨⟨_, hxU⟩⟩
  let κ : k →+* Γ(M, U) := (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  let pchar := ringExpChar k
  haveI : ExpChar M.functionField pchar :=
    expChar_of_injective_ringHom
      (f := (M.germToFunctionField U).hom.comp κ) (RingHom.injective _) pchar
  haveI : ExpChar ((U'.2.primeIdealOf ⟨jE.fromNormalization d'.1, hxU⟩).asIdeal).ResidueField
      pchar :=
    expChar_of_injective_ringHom
      (f := (algebraMap Γ(M, U)
        ((U'.2.primeIdealOf ⟨jE.fromNormalization d'.1, hxU⟩).asIdeal).ResidueField).comp κ)
      (RingHom.injective _) pchar
  exact schemeFieldExtensionNormalization_divisorDelta_eq_genericDegree M Y.functionField
    U' d' hxU pchar

#print axioms schemeDivisorDelta_of_isIso
#print axioms schemeGenericInclusion_comp_eq_fieldExtensionInclusion
#print axioms schemeDivisorDelta_eq_finrank_of_purelyInseparable

end
end Pcf
