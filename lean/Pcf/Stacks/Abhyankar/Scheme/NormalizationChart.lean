/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Charts

/-!
# The normalization of `X` in `Y` on affine charts

Mathlib's relative normalization `(g : Y ⟶ X).normalization` (Stacks Section 29.53, Tag `035H`)
with structure morphism `π = g.fromNormalization`:

* `normalizationAppAlgEquiv`: over an affine open `V ⊂ X`, `Γ(Y', π⁻¹V)` is the integral closure
  of `Γ(X, V)` in `Γ(Y, g⁻¹V)`, as `Γ(X, V)`-algebras;
* `exists_iso_normalization_restrict`: if `g = f ≫ U.ι` with `f : Y → U` integral, then
  `π⁻¹U ≅ Y` over `U` (clause (1) of Stacks Tag `0EYH`; the proof uses Mathlib's
  `normalizationPullback`, normalization commutes with smooth base change, Tag `03GV`);
* `ideal_vanishingIdeal_eq_radical`: the ideal of the reduced closed subscheme on a closed set
  `Z` over an affine open `W` on which `Z = V(s)` is `√(s)`; this computes
  `D' = π⁻¹(D)_red` of `0EYH` on charts.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Stacks.SchemeLevel

/-- In a pullback of `f ≫ g` along a monomorphism `g`, `fst ≫ f = snd`. -/
theorem fst_comp_eq_snd_of_mono {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) [Mono g] :
    pullback.fst (f ≫ g) g ≫ f = pullback.snd (f ≫ g) g := by
  rw [← cancel_mono g, Category.assoc, pullback.condition]

instance isIso_fst_of_mono {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) [Mono g] :
    IsIso (pullback.fst (f ≫ g) g) := by
  refine ⟨pullback.lift (𝟙 Y) f (by simp), ?_, by simp⟩
  apply pullback.hom_ext
  · simp
  · simp [fst_comp_eq_snd_of_mono]

/-- **Stacks Tag `0EYH`, clause (1).**  For `f : Y → U ⊂ X` integral, the restriction to `U` of
the normalization of `X` in `Y` is `Y`, over `U`. -/
theorem exists_iso_normalization_restrict {X Y : Scheme.{u}} (U : X.Opens) (f : Y ⟶ U)
    [IsIntegralHom f] [QuasiCompact (f ≫ U.ι)] [QuasiSeparated (f ≫ U.ι)] :
    ∃ e : Y ≅ ((f ≫ U.ι).fromNormalization ⁻¹ᵁ U).toScheme,
      e.hom ≫ ((f ≫ U.ι).fromNormalization ∣_ U) = f := by
  let s := pullback.snd (f ≫ U.ι) U.ι
  have hs : pullback.fst (f ≫ U.ι) U.ι ≫ f = s := fst_comp_eq_snd_of_mono f U.ι
  have : IsIntegralHom s := by
    rw [← hs]; infer_instance
  refine ⟨(asIso (pullback.fst (f ≫ U.ι) U.ι)).symm ≪≫ asIso s.toNormalization ≪≫
    asIso ((f ≫ U.ι).normalizationPullback U.ι) ≪≫
    pullbackRestrictIsoRestrict (f ≫ U.ι).fromNormalization U, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_morphismRestrict, Scheme.Hom.normalizationPullback_snd]
  rw [IsIso.inv_comp_eq, hs]
  exact s.toNormalization_fromNormalization

/-- Over an affine open `V ⊂ X`, the ring of sections of the normalization of `X` in `Y` over
`V` is the integral closure of `Γ(X, V)` in `Γ(Y, g⁻¹V)`, as `Γ(X, V)`-algebras. -/
noncomputable def normalizationAppAlgEquiv {X Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g]
    [QuasiSeparated g] {V : X.Opens} (hV : IsAffineOpen V) :
    letI := (g.app V).hom.toAlgebra
    letI := (g.fromNormalization.app V).hom.toAlgebra
    Γ(g.normalization, g.fromNormalization ⁻¹ᵁ V) ≃ₐ[Γ(X, V)]
      integralClosure Γ(X, V) Γ(Y, g ⁻¹ᵁ V) :=
  letI := (g.app V).hom.toAlgebra
  letI := (g.fromNormalization.app V).hom.toAlgebra
  { toRingEquiv := (g.normalizationObjIso hV).commRingCatIsoToRingEquiv
    commutes' := fun r ↦ by
      change (g.normalizationObjIso hV).hom ((g.fromNormalization.app V).hom r) = _
      rw [Scheme.Hom.fromNormalization_app g hV]
      change ((g.normalizationObjIso hV).inv ≫ (g.normalizationObjIso hV).hom).hom _ = _
      rw [Iso.inv_hom_id]
      rfl }

/-- The ideal of the reduced induced closed subscheme on `Z` over an affine open `W` on which
`Z = V(s)` is the radical of `(s)`. -/
theorem ideal_vanishingIdeal_eq_radical {S : Scheme.{u}} (Z : TopologicalSpace.Closeds S)
    (W : S.affineOpens) (s : Γ(S, W)) (hZ : ∀ y ∈ W.1, y ∈ Z ↔ y ∉ S.basicOpen s) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal W = (Ideal.span {s}).radical := by
  have h : W.2.fromSpec ⁻¹' (Z : Set S) = PrimeSpectrum.zeroLocus {s} := by
    ext p
    have hp : W.2.fromSpec p ∈ W.1 := by
      rw [← SetLike.mem_coe, ← W.2.range_fromSpec]; exact Set.mem_range_self p
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [hZ _ hp]
    change ¬ (p ∈ W.2.fromSpec ⁻¹ᵁ S.basicOpen s) ↔ _
    rw [W.2.fromSpec_preimage_basicOpen]
    exact ⟨fun h ↦ Set.singleton_subset_iff.mpr (not_not.mp h),
      fun h hs ↦ hs (Set.singleton_subset_iff.mp h)⟩
  refine (congrArg PrimeSpectrum.vanishingIdeal h).trans ?_
  rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]

#print axioms fst_comp_eq_snd_of_mono
#print axioms isIso_fst_of_mono
#print axioms exists_iso_normalization_restrict
#print axioms normalizationAppAlgEquiv
#print axioms ideal_vanishingIdeal_eq_radical

end Pcf.Stacks.SchemeLevel
