/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeExtraction
public import Pcf.Stacks.Purity.NormalizationTower
public import Pcf.Stacks.Abhyankar.Scheme.ManuscriptRootCover

/-!
# `V` is the normalization of `U` in `W` (proof of `thm:bounding`, Step 2)

The proof of `thm:bounding` in paper-p asserts: "`V` is the normalization of `U` in `W`: the
normalization of `U` in `W` factors through the finite morphism `V → U` (Stacks `035I`(2)), and
the normal ring of an affine open of `V` is integrally closed in the ring of functions on its
dense open intersection with `W` (Stacks `030C`)."

* `isIntegrallyClosedIn_restrict` — for an integral normal scheme `V`, a nonempty affine open `T`
  and a nonempty open `T' ≤ T`, `Γ(V, T)` is integrally closed in `Γ(V, T')` (the `030C` step).
* `opensι_fromNormalization_isIso` — the normalization of `V` in a nonempty open `W ⊂ V` is `V`.
* `normalizationDesc_opensι_isIso` — for `g : V → U` integral, the factorization map of `035I`(2)
  from the normalization of `U` in `W` to `V` is an isomorphism
  (`Pcf.Stacks.normalizationDesc_isIso_of_fromNormalization_isIso`).
* `boundingStep2_rootCoverAlong_of_normal` — the base-change identity of Step 2 for
  `V` itself, with no normalization hypothesis.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Bounding.PaperPBoundingNormalization

open Pcf.Stacks.SchemeLevel

set_option linter.style.haveILetI false

variable {V : Scheme.{u}} [IsIntegral V] [Pcf.IsNormalScheme V] [IsLocallyNoetherian V]

omit [IsLocallyNoetherian V] in
/-- **Stacks `030C` step.**  On an integral normal scheme, for a nonempty affine open `T` and a
nonempty open `T' ≤ T`, `Γ(V, T)` is integrally closed in `Γ(V, T')`. -/
theorem isIntegrallyClosedIn_restrict {T T' : V.Opens} (hT : IsAffineOpen T) (h : T' ≤ T)
    [Nonempty T'] :
    letI := (V.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsIntegrallyClosedIn Γ(V, T) Γ(V, T') := by
  letI := (V.presheaf.map (homOfLE h).op).hom.toAlgebra
  have : Nonempty T := ⟨⟨(Classical.arbitrary T').1, h (Classical.arbitrary T').2⟩⟩
  have : IsIntegrallyClosed Γ(V, T) := Pcf.IsNormalScheme.component_integrallyClosed ⟨T, hT⟩
  have hfrac : IsFractionRing Γ(V, T) V.functionField :=
    functionField_isFractionRing_of_isAffineOpen V T hT
  have hcomp : ∀ r : Γ(V, T), V.germToFunctionField T' (algebraMap _ _ r) =
      V.germToFunctionField T r := fun r ↦ by
    change (V.presheaf.map (homOfLE h).op ≫ V.presheaf.germ T' _ _) r = _
    rw [TopCat.Presheaf.germ_res]
  refine isIntegrallyClosedIn_iff.mpr ⟨map_injective_of_isIntegral V (homOfLE h), ?_⟩
  intro x hx
  have hK : IsIntegral Γ(V, T) (V.germToFunctionField T' x) :=
    IsIntegral.map_of_comp_eq (RingHom.id _) (V.germToFunctionField T').hom
      (by ext r; exact (hcomp r).symm) hx
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hK
  refine ⟨r, V.germToFunctionField_injective T' ?_⟩
  rw [hcomp]
  exact hr

omit [IsLocallyNoetherian V] in
/-- The ring map `Γ(V, T) → Γ(W, W.ι⁻¹ T)` is injective with integrally closed image. -/
theorem isIntegrallyClosedIn_opensι_app (W : V.Opens) [Nonempty W] {T : V.Opens}
    (hT : IsAffineOpen T) [Nonempty T] :
    letI := (W.ι.app T).hom.toAlgebra
    IsIntegrallyClosedIn Γ(V, T) Γ(W.toScheme, W.ι ⁻¹ᵁ T) := by
  have hne : Nonempty (W.ι ''ᵁ W.ι ⁻¹ᵁ T) := by
    obtain ⟨⟨t, ht⟩⟩ := ‹Nonempty T›
    obtain ⟨⟨w, hw⟩⟩ := ‹Nonempty W›
    have hirr : IsPreirreducible (Set.univ : Set V) :=
      (IrreducibleSpace.isIrreducible_univ V).isPreirreducible
    obtain ⟨z, -, hzW, hzT⟩ := hirr W T W.isOpen T.isOpen ⟨w, trivial, hw⟩ ⟨t, trivial, ht⟩
    refine ⟨⟨z, ?_⟩⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hzW, hzT⟩
  have := isIntegrallyClosedIn_restrict hT (W.ι.image_preimage_le T)
  rw [Scheme.Opens.ι_app]
  exact this

/-- **The normalization of an integral normal scheme in a nonempty open is the scheme itself.** -/
theorem opensι_fromNormalization_isIso (W : V.Opens) [Nonempty W] :
    IsIso W.ι.fromNormalization := by
  let U (i : V) : V.Opens := by
    letI : IsOpenImmersion (V.affineCover.f i) := V.affineCover.map_prop i
    exact (V.affineCover.f i).opensRange
  have hcover : iSup U = ⊤ := by
    change ⨆ i, (V.affineCover.f i).opensRange = ⊤
    exact V.affineCover.iSup_opensRange
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := .isomorphisms _) U hcover).mpr fun i ↦ ?_
  letI : IsOpenImmersion (V.affineCover.f i) := V.affineCover.map_prop i
  have hU : IsAffineOpen (U i) := isAffineOpen_opensRange (V.affineCover.f i)
  refine (isIso_morphismRestrict_iff_isIso_app W.ι.fromNormalization hU).mpr ?_
  rcases isEmpty_or_nonempty (U i) with hE | hNE
  · have hbot : U i = ⊥ := by
      ext x
      exact ⟨fun hx ↦ (hE.false ⟨x, hx⟩).elim, fun hx ↦ hx.elim⟩
    rw [hbot]
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hcod : Subsingleton Γ(W.ι.normalization, W.ι.fromNormalization ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstance : Subsingleton Γ(W.ι.normalization, ⊥))
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩
  letI := (W.ι.app (U i)).hom.toAlgebra
  have hnormal := isIntegrallyClosedIn_opensι_app W hU
  let B := integralClosure Γ(V, U i) Γ(W.toScheme, W.ι ⁻¹ᵁ U i)
  have hbij : Function.Bijective (algebraMap Γ(V, U i) B) := by
    constructor
    · intro a b hab
      apply (isIntegrallyClosedIn_iff.mp hnormal).1
      exact congrArg (Subalgebra.val B) hab
    · intro x
      obtain ⟨s, hs⟩ := (isIntegrallyClosedIn_iff.mp hnormal).2 x.property
      exact ⟨s, Subtype.ext hs⟩
  rw [W.ι.fromNormalization_app hU]
  haveI : IsIso (CommRingCat.ofHom (algebraMap Γ(V, U i) B)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance

/-- **Stacks `035I`(2) + `030C`.**  If `g : V → U` is integral, `V` integral and normal, and
`W ⊂ V` a nonempty open, the factorization map from the normalization of `U` in `W` to `V` is an
isomorphism: `V` is the normalization of `U` in `W`. -/
theorem normalizationDesc_opensι_isIso {U : Scheme.{u}} (g : V ⟶ U) [IsIntegralHom g]
    (W : V.Opens) [Nonempty W] [QuasiCompact (W.ι ≫ g)] [QuasiSeparated (W.ι ≫ g)] :
    IsIso ((W.ι ≫ g).normalizationDesc W.ι g rfl) := by
  haveI := opensι_fromNormalization_isIso W
  exact Pcf.Stacks.normalizationDesc_isIso_of_fromNormalization_isIso W.ι g

/-- The manuscript data of Step 2 with `V → U` replaced by an arbitrary `h` equal to
`W.ι ≫ g`. -/
theorem rootCoverAlong_of_eq {U : Scheme.{u}} {D : U.IdealSheafData} (g : V ⟶ U)
    [IsIntegralHom g] (W : V.Opens) [Nonempty W]
    (h : W.toScheme ⟶ U) [QuasiCompact h] [QuasiSeparated h] (hh : h = W.ι ≫ g)
    (H : IsEtaleLocallyRootCoverAlong D h.fromNormalization) :
    IsEtaleLocallyRootCoverAlong D g := by
  subst hh
  haveI := normalizationDesc_opensι_isIso g W
  exact H.of_iso (asIso ((W.ι ≫ g).normalizationDesc W.ι g rfl)).symm
    (by simp [Scheme.Hom.normalizationDesc_comp])

/-- **The base-change identity of Step 2 of the proof of `thm:bounding`, for `V` itself.**

Let `U` be locally Noetherian, `B_U = D ⊂ U` an effective Cartier divisor that is a regular
scheme, `g = f_V : V → U` finite with `V` integral and normal, and suppose the restriction
`W = g⁻¹(U ∖ D) → U ∖ D` is (finite) étale and tamely ramified over `U` in codimension one, with
`W` nonempty.  Then every point of `U` is in the image of an étale `ρ : U' = Spec R → U` with
`B_U ×_U U' = V(a)` and `V ×_U U' ≅ ∐_i Spec R[z_i]/(z_i^{e_i} - u_i a)`.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem boundingStep2_rootCoverAlong_of_normal {U : Scheme.{u}} [IsLocallyNoetherian U]
    {D : U.IdealSheafData} (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (g : V ⟶ U) [IsFinite g] [Nonempty (g ⁻¹ᵁ complementOpen D)]
    [Etale (g ∣_ complementOpen D)]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) (g ∣_ complementOpen D)) :
    IsEtaleLocallyRootCoverAlong D g := by
  have H := abhyankarLemma_normalization_rootCoverAlong hD hDreg (g ∣_ complementOpen D) htame
  exact rootCoverAlong_of_eq g (g ⁻¹ᵁ complementOpen D) _ (morphismRestrict_ι g _) H

end Pcf.Bounding.PaperPBoundingNormalization
