/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Tag0EYH
public import Pcf.Stacks.Abhyankar.Scheme.EffectiveCartier
public import Pcf.Stacks.Abhyankar.FiniteNormalization

/-!
# Abhyankar's lemma with one divisor equation (paper-p, after `thm:abhyankar`)

The manuscript (`latex/paper-p.tex`, display after `thm:abhyankar`, and Step 2 of the proof of
`thm:bounding`) uses Abhyankar's lemma in the form: every point of `U` is in the image of an
étale `U' = Spec R → U` with
`D ×_U U' = V(a)`, `a` a nonzerodivisor with `R/aR` regular, and
`V ×_U U' ≅ ∐_i Spec R[z_i]/(z_i^{e_i} - u_i a)` with `e_i` invertible and `u_i ∈ Rˣ`;
the *same* `a` occurs in every piece and cuts out `D`.  The tag-form theorem
`abhyankarLemma_normalization` (Stacks `0EYH`) allows an independent `f_i` per piece.  The common
`a` is legitimate because `D` is an effective Cartier divisor: on an affine chart `V` it is cut
out by one nonzerodivisor `a`, the proof of `0EYG` keeps that equation, and it pulls back to an
equation of `D ×_X Spec A` (`comap_chart_eq_ofIdealTop`).

## Main results

* `IsEtaleLocallyRootCoverAlong D π` — the manuscript's local form, with
  `D ×_X Spec A = V(a)` stated as `D.comap φ = ofIdealTop (a)`.
* `abhyankarLemma_normalization_rootCoverAlong` — display after `thm:abhyankar`.
* `boundingStep2_rootCoverAlong`, `IsEtaleLocallyRootCoverAlong.of_iso` — the base-change identity
  of Step 2 of `thm:bounding` for any `V → U` isomorphic over `U` to the normalization.
* `standardRing_finite_free_and_etale_away` — the standard tamely ramified morphism is finite
  free and étale over `Spec R_a`.
* `isTamelyRamifiedInCodimensionOne_of_isUnit_natCast` — "over a field of characteristic zero
  every finite étale cover is tamely ramified in codimension one", in the setting of
  `thm:abhyankar`; `abhyankarLemma_normalization_rootCoverAlong_of_isUnit_natCast` combines it.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Pcf.Stacks.SchemeLevel

/-- On affine schemes, pullback of an ideal sheaf is extension of its global ideal. -/
theorem ideal_comap_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (D : Y.IdealSheafData) (f : X ⟶ Y) :
    (D.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (D.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let J : X.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop ((D.ideal U).map f.appTop.hom)
  have hJ : J.ideal V = (D.ideal U).map f.appTop.hom := by
    simp only [J, Scheme.IdealSheafData.ofIdealTop_ideal]
    change Ideal.map
      (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op).hom _ = _
    have hid : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op =
        𝟙 (Opposite.op (⊤ : X.Opens)) := Subsingleton.elim _ _
    rw [hid, X.presheaf.map_id, CommRingCat.hom_id, Ideal.map_id]
  have hmap (K : X.IdealSheafData) :
      (K.map f).ideal U = (K.ideal V).comap f.appTop.hom := by
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    rfl
  have hD : D ≤ J.map f := by
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [hmap, hJ]
    exact Ideal.le_comap_map
  have hleft : (D.comap f).ideal V ≤ J.ideal V :=
    (Scheme.IdealSheafData.le_map_iff_comap_le.mp hD) V
  have hright : (D.ideal U).map f.appTop.hom ≤ (D.comap f).ideal V := by
    have h := D.le_map_comap f
    have h' : D.ideal U ≤ ((D.comap f).ideal V).comap f.appTop.hom := by
      simpa only [hmap] using h U
    exact Ideal.map_le_iff_le_comap.mpr h'
  exact le_antisymm (hleft.trans_eq hJ) hright

/-- The global ideal of `D ×_X Spec Γ(X, V)`, for `D` cut out by `b` on the affine open `V`. -/
theorem ideal_comap_fromSpec {X : Scheme.{u}} (D : X.IdealSheafData) {V : X.Opens}
    (hV : IsAffineOpen V) {b : Γ(X, V)} (hDb : D.ideal ⟨V, hV⟩ = Ideal.span {b}) :
    (D.comap hV.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso Γ(X, V)).inv b} := by
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion D hV.fromSpec
    ⟨⊤, isAffineOpen_top _⟩
  rw [h1]
  have hW : hV.fromSpec ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  have hW' : ∀ W : X.affineOpens, (h : W.1 = V) → D.ideal W =
      Ideal.span {(X.presheaf.map (eqToHom (congrArg Opposite.op h.symm) :
        Opposite.op V ⟶ Opposite.op W.1)).hom b} := by
    intro W h
    rw [← D.map_ideal' (U := W) (V := ⟨V, hV⟩) (eqToHom (congrArg Opposite.op h.symm)), hDb,
      Ideal.map_span, Set.image_singleton]
  rw [hW' _ hW]
  have hcomap : ∀ J : Ideal Γ(X, hV.fromSpec ''ᵁ ⊤),
      J.comap (hV.fromSpec.appIso ⊤).inv.hom = J.map (hV.fromSpec.appIso ⊤).hom.hom := fun J ↦
    Ideal.comap_symm (I := J) (hV.fromSpec.appIso ⊤).commRingCatIsoToRingEquiv
  have key : X.presheaf.map (eqToHom (congrArg Opposite.op hW.symm) :
        Opposite.op V ⟶ Opposite.op (hV.fromSpec ''ᵁ ⊤)) ≫ (hV.fromSpec.appIso ⊤).hom =
      (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [Scheme.Hom.appIso_hom, ← Category.assoc, Scheme.Hom.naturality, Category.assoc,
      hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    conv_rhs => rw [← Category.comp_id (Scheme.ΓSpecIso Γ(X, V)).inv]
    congr 1
  erw [hcomap, Ideal.map_span, Set.image_singleton, ← CommRingCat.comp_apply, key]

/-- The global ideal of an ideal sheaf of the form `ofIdealTop I`. -/
theorem ofIdealTop_ideal_top {Z : Scheme.{u}} [IsAffine Z] (I : Ideal Γ(Z, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top Z⟩ = I := by
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  change Ideal.map (Z.presheaf.map (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)).op).hom _ = _
  have hid : (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op (⊤ : Z.Opens)) :=
    Subsingleton.elim _ _
  rw [hid, Z.presheaf.map_id, CommRingCat.hom_id, Ideal.map_id]

/-- **`D ×_X Spec A = V(b)` on an affine chart.**  If `D` is cut out by `b` on the affine open
`V` and `A` is a `Γ(X, V)`-algebra, then the pullback of `D` along
`Spec A → Spec Γ(X, V) ≅ V ⊂ X` is the closed subscheme `V(b) ⊂ Spec A`. -/
theorem comap_chart_eq_ofIdealTop {X : Scheme.{u}} (D : X.IdealSheafData) {V : X.Opens}
    (hV : IsAffineOpen V) {b : Γ(X, V)} (hDb : D.ideal ⟨V, hV⟩ = Ideal.span {b})
    (A : Type u) [CommRing A] [Algebra Γ(X, V) A] :
    D.comap (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap Γ(X, V) A b)}) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.comap_comp, ideal_comap_of_isAffine, ideal_comap_fromSpec D hV hDb,
    ofIdealTop_ideal_top, Ideal.map_span, Set.image_singleton]
  congr 2
  exact congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap Γ(X, V) A))) b).symm

/-- The manuscript form of the local structure in Abhyankar's lemma (paper-p, display after
`thm:abhyankar`): every point of `X` is in the image of an étale `φ : U' = Spec A → X` such that
`D ×_X U' = V(a)` for one `a ∈ A`, a nonzerodivisor with `A/aA` regular, and
`Y' ×_X U' ≅ ∐_i Spec A[z_i]/(z_i^{e_i} - u_i a)` over `U'`, with `e_i ≥ 1` invertible in `A`
and `u_i ∈ Aˣ`.  The identity `D ×_X U' = V(a)` is stated as equality of ideal sheaves on
`Spec A`: the pullback `D.comap φ` (whose closed subscheme is `D ×_X Spec A`, Mathlib's
`IdealSheafData.comapIso`) is the ideal sheaf of `(a)`. -/
def IsEtaleLocallyRootCoverAlong {X Y : Scheme.{u}} (D : X.IdealSheafData) (π : Y ⟶ X) :
    Prop :=
  ∀ x : X, ∃ (A : CommRingCat.{u}) (φ : Spec A ⟶ X), Etale φ ∧ x ∈ Set.range φ.base ∧
    IsNoetherianRing A ∧ ∃ a : A, a ∈ nonZeroDivisors A ∧ IsRegularRing (A ⧸ Ideal.span {a}) ∧
      D.comap φ =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso A).inv a}) ∧
      ∃ (n : ℕ) (e : Fin n → ℕ) (w : Fin n → Aˣ), (∀ i, 1 ≤ e i ∧ IsUnit (e i : A)) ∧
        ∃ ψ : pullback π φ ≅
            ∐ (fun i ↦ Spec (CommRingCat.of (standardRing A ((w i : A) * a) (e i)))),
          ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
            (algebraMap A (standardRing A ((w i : A) * a) (e i))))) = pullback.snd π φ

/-- The chart morphism `Spec A → Spec Γ(X, V) ≅ V ⊂ X` of an étale `Γ(X, V)`-algebra is étale,
and contains `x` in its image if `A` has a prime over the prime of `x`. -/
theorem etale_chart {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hx : x ∈ V)
    (A : Type u) [CommRing A] [Algebra Γ(X, V) A] [Algebra.Etale Γ(X, V) A]
    (hy : ∃ y' : PrimeSpectrum A, y'.asIdeal.under Γ(X, V) = (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec) ∧
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec).base := by
  refine ⟨?_, ?_⟩
  · have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    infer_instance
  · obtain ⟨y', hy'⟩ := hy
    refine ⟨y', ?_⟩
    have hc : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) y' =
        hV.primeIdealOf ⟨x, hx⟩ := PrimeSpectrum.ext hy'
    change hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) y') = x
    rw [hc, hV.fromSpec_primeIdealOf]

variable {X Y : Scheme.{u}} {D : X.IdealSheafData}

/-- `A[x]/(x - 1·1) ≅ A`. -/
noncomputable def standardRingUnitOneEquiv (A : Type u) [CommRing A] :
    standardRing A (((1 : Aˣ) : A) * 1) 1 ≃ₐ[A] A :=
  (Ideal.quotientEquivAlgOfEq A (by simp)).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (1 : A))

/-- The manuscript local structure at a point `x ∉ D`. -/
theorem exists_rootCoverAlong_of_notMem [IsLocallyNoetherian X] (hD : IsEffectiveCartier D)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f] (x : X) (hxD : x ∉ D.support) :
    ∃ (A : CommRingCat.{u}) (φ : Spec A ⟶ X), Etale φ ∧ x ∈ Set.range φ.base ∧
      IsNoetherianRing A ∧ ∃ a : A, a ∈ nonZeroDivisors A ∧
        IsRegularRing (A ⧸ Ideal.span {a}) ∧
        D.comap φ =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso A).inv a}) ∧
        ∃ (n : ℕ) (e : Fin n → ℕ) (w : Fin n → Aˣ), (∀ i, 1 ≤ e i ∧ IsUnit (e i : A)) ∧
          ∃ ψ : pullback (f ≫ (complementOpen D).ι).fromNormalization φ ≅
              ∐ (fun i ↦ Spec (CommRingCat.of (standardRing A ((w i : A) * a) (e i)))),
            ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
              (algebraMap A (standardRing A ((w i : A) * a) (e i))))) =
              pullback.snd (f ≫ (complementOpen D).ι).fromNormalization φ := by
  obtain ⟨V, hxV, hVU⟩ := exists_affine_le_complement hD hxD
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨-, hfin, het⟩ := finite_etale_of_le f hVU
  let _ : Algebra Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
  let _ : Algebra Γ(X, V) Γ((f ≫ (complementOpen D).ι).normalization,
      (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).fromNormalization.app V.1).hom.toAlgebra
  have hpre : IsAffineOpen ((f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
    V.2.preimage _
  have htop : integralClosure Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) = ⊤ :=
    integralClosure_eq_top_iff.mpr (Algebra.IsIntegral.of_finite _ _)
  let E : Γ((f ≫ (complementOpen D).ι).normalization,
      (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) ≃ₐ[Γ(X, V)]
        Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    (normalizationAppAlgEquiv (f ≫ (complementOpen D).ι) V.2).trans
      ((Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv)
  obtain ⟨A, _, _, hAet, hy', hAN, n, ⟨g⟩⟩ :=
    hasSplitCoverAt_of_finite_etale Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1)
      (V.2.primeIdealOf ⟨x, hxV⟩)
  let F := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[Γ(X, V)] A) E
  let F' : A ⊗[Γ(X, V)] Γ((f ≫ (complementOpen D).ι).normalization,
      (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) ≃ₐ[A]
        A ⊗[Γ(X, V)] Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    AlgEquiv.ofRingEquiv (f := F.toRingEquiv) fun x ↦ by
      change F (x ⊗ₜ 1) = x ⊗ₜ 1
      simp only [F, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
      rfl
  let g' := (F'.trans g).trans (AlgEquiv.piCongrRight fun _ ↦
    (standardRingUnitOneEquiv A).symm)
  obtain ⟨ψ, hψ⟩ := exists_pullback_iso_sigma
    (f ≫ (complementOpen D).ι).fromNormalization V.2 hpre A
    (fun _ : Fin n ↦ standardRing A (((1 : Aˣ) : A) * 1) 1) g'
  obtain ⟨hφ, hxφ⟩ := etale_chart V.2 hxV A hy'
  have hD1 : D.ideal ⟨V.1, V.2⟩ = Ideal.span {(1 : Γ(X, V))} := by
    rw [Ideal.span_singleton_one]
    exact ideal_eq_top_of_disjoint D V fun y hy ↦ hVU hy
  refine ⟨CommRingCat.of A, _, hφ, hxφ, hAN, 1, one_mem _, ?_, ?_, n, fun _ ↦ 1, fun _ ↦ 1,
    fun _ ↦ ⟨le_rfl, by simp⟩, ψ, hψ⟩
  · have : Subsingleton (A ⧸ Ideal.span {(1 : A)}) := by
      rw [Ideal.span_singleton_one]; infer_instance
    exact isRegularRing_of_subsingleton _
  · rw [comap_chart_eq_ofIdealTop D V.2 hD1 A, map_one]

/-- The manuscript local structure at a point `x ∈ D`: the étale chart of `0EYG`/`0EYH` keeps
the local equation `a` of `D`, so that `D ×_X Spec A = V(a)` and every piece is
`A[z]/(z^e - u a)` for this one `a`. -/
theorem exists_rootCoverAlong_of_mem [IsLocallyNoetherian X] (hA : AbhyankarLemmaTameOver X)
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) (x : X) (hxD : x ∈ D.support) :
    ∃ (A : CommRingCat.{u}) (φ : Spec A ⟶ X), Etale φ ∧ x ∈ Set.range φ.base ∧
      IsNoetherianRing A ∧ ∃ a : A, a ∈ nonZeroDivisors A ∧
        IsRegularRing (A ⧸ Ideal.span {a}) ∧
        D.comap φ =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso A).inv a}) ∧
        ∃ (n : ℕ) (e : Fin n → ℕ) (w : Fin n → Aˣ), (∀ i, 1 ≤ e i ∧ IsUnit (e i : A)) ∧
          ∃ ψ : pullback (f ≫ (complementOpen D).ι).fromNormalization φ ≅
              ∐ (fun i ↦ Spec (CommRingCat.of (standardRing A ((w i : A) * a) (e i)))),
            ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
              (algebraMap A (standardRing A ((w i : A) * a) (e i))))) =
              pullback.snd (f ≫ (complementOpen D).ι).fromNormalization φ := by
  obtain ⟨V, hxV, a, ha, hDa⟩ := hD x
  have hpre : IsAffineOpen ((f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
    V.2.preimage _
  have hy : a ∈ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    have := (mem_support_iff_of_ideal_eq hDa hxV).mp hxD
    rwa [mem_basicOpen_iff_notMem_primeIdealOf V.2 a ⟨x, hxV⟩, not_not] at this
  obtain ⟨-, -, -, -, hstr⟩ := normalization_appTop_algEquiv_standardCovers_of_chart hA hDreg f
      htame ha hDa
  let _ : Algebra Γ(X, V) Γ((f ≫ (complementOpen D).ι).normalization,
      (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).fromNormalization.app V.1).hom.toAlgebra
  obtain ⟨A, _, _, hAet, hy', hAN, haA, hregA, n, e, w, he, heu, ⟨g⟩⟩ := hstr _ hy
  obtain ⟨ψ, hψ⟩ := exists_pullback_iso_sigma
    (f ≫ (complementOpen D).ι).fromNormalization V.2 hpre A
    (fun i ↦ standardRing A ((w i : A) * algebraMap Γ(X, V) A a) (e i)) g
  obtain ⟨hφ, hxφ⟩ := etale_chart V.2 hxV A hy'
  exact ⟨CommRingCat.of A, _, hφ, hxφ, hAN, algebraMap Γ(X, V) A a, haA, hregA,
    comap_chart_eq_ofIdealTop D V.2 hDa A, n, e, w, fun i ↦ ⟨he i, heu i⟩, ψ, hψ⟩

/-- **Abhyankar's lemma with one divisor equation (paper-p, the display after
`thm:abhyankar`), with the affine statement as a hypothesis.** -/
theorem abhyankarLemma_normalization_rootCoverAlong_of_abhyankarLemmaTameOver
    [IsLocallyNoetherian X] (hA : AbhyankarLemmaTameOver X)
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    IsEtaleLocallyRootCoverAlong D (f ≫ (complementOpen D).ι).fromNormalization := by
  intro x
  by_cases hxD : x ∈ D.support
  · exact exists_rootCoverAlong_of_mem hA hD hDreg f htame x hxD
  · exact exists_rootCoverAlong_of_notMem hD f x hxD

/-- **Abhyankar's lemma in the form displayed after `thm:abhyankar` in paper-p.**

Let `X` be locally Noetherian, `D ⊂ X` an effective Cartier divisor that is a regular scheme,
`f : Y → X ∖ D` finite étale and tamely ramified over `X` in codimension one, and
`π : Y' → X` the normalization of `X` in `Y`.  Then every point of `X` is in the image of an
étale `φ : U' = Spec A → X` such that `D ×_X U' = V(a)` with `a ∈ A` a nonzerodivisor and
`A/aA` regular, and
`Y' ×_X U' ≅ ∐_{i ∈ I} Spec A[z_i]/(z_i^{e_i} - u_i a)` over `U'`
for a finite set `I`, integers `e_i ≥ 1` invertible in `A` and units `u_i ∈ Aˣ`.

**Divergence from Stacks.**  The statement of Stacks Lemma 58.31.6 (Tag `0EYH`,
`abhyankarLemma_normalization`) gives each piece its own nonzerodivisor `f_i` with `A/f_iA`
regular, and does not relate the `f_i` to `D`.  The single equation `a` of `D ×_X U'` is what
the *proof* of Lemma 58.31.5 (Tag `0EYG`) produces ("`D ⊂ X` is given by a nonzerodivisor
`f ∈ A`", and the pieces are `A_λ[x]/(x^{e_i} - f)`); it is legitimate because `D` is an
effective Cartier divisor, so it has one local equation on an affine chart, and that equation
pulls back to an equation of `D ×_X U'`.  The units `u_i` are a harmless weakening of the
`u_i = 1` of the Stacks proof: pcf's affine layer
(`Pcf.Stacks.AbhyankarLemmaTameOfFinite`) produces `x^{e_i} - u_i a`.  This theorem is therefore
a strengthening of the tag's literal statement and is not tagged; the tag-form theorem is
`abhyankarLemma_normalization`.

`paper-p.tex` correspondence: Theorem 6.5 (`thm:abhyankar`), Theorem 7.5 (`thm:bounding`). -/
theorem abhyankarLemma_normalization_rootCoverAlong [IsLocallyNoetherian X]
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    IsEtaleLocallyRootCoverAlong D (f ≫ (complementOpen D).ι).fromNormalization :=
  abhyankarLemma_normalization_rootCoverAlong_of_abhyankarLemmaTameOver
    (abhyankarLemmaTameOver_of_forall X Pcf.Stacks.abhyankarLemmaTameOfFinite) hD hDreg f htame

/-- The manuscript local structure is invariant under isomorphism over `X`: if `g : V → X` is
isomorphic over `X` to `π`, then `g` has the same étale-local presentation. -/
theorem IsEtaleLocallyRootCoverAlong.of_iso {V Y' : Scheme.{u}} {π : Y' ⟶ X} {g : V ⟶ X}
    (h : IsEtaleLocallyRootCoverAlong D π) (e : V ≅ Y') (he : e.hom ≫ π = g) :
    IsEtaleLocallyRootCoverAlong D g := by
  intro x
  obtain ⟨A, φ, hφ, hx, hN, a, ha, hreg, hDφ, n, ee, w, hee, ψ, hψ⟩ := h x
  let θ : pullback g φ ≅ pullback π φ :=
    asIso (pullback.map g φ π φ e.hom (𝟙 _) (𝟙 _) (by simp [he]) (by simp))
  refine ⟨A, φ, hφ, hx, hN, a, ha, hreg, hDφ, n, ee, w, hee, θ ≪≫ ψ, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hψ]
  simp [θ]

/-- **The base-change identity of the proof of `thm:bounding` (paper-p, Step 2).**  If `g : V → U`
is the normalization of `U` in the finite étale `W → U ∖ B_U`, up to isomorphism over `U`, then
every point of `U` is in the image of an étale `ρ : U' = Spec R → U` with
`B_U ×_U U' = V(a)` and `V ×_U U' ≅ ∐_i Spec R[z_i]/(z_i^{e_i} - u_i a)`. -/
theorem boundingStep2_rootCoverAlong [IsLocallyNoetherian X]
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f)
    {V : Scheme.{u}} (g : V ⟶ X)
    (e : V ≅ (f ≫ (complementOpen D).ι).normalization)
    (he : e.hom ≫ (f ≫ (complementOpen D).ι).fromNormalization = g) :
    IsEtaleLocallyRootCoverAlong D g :=
  (abhyankarLemma_normalization_rootCoverAlong hD hDreg f htame).of_iso e he

/-- **The standard tamely ramified morphism (paper-p, prose before `thm:abhyankar`).**  For a
unit `u`, any `a` and `e ≥ 1` invertible in `R`, the morphism
`Spec R[z]/(z^e - u a) → Spec R` is finite locally free (here: `R[z]/(z^e - u a)` is a finite free
`R`-module) and étale over `Spec R_a`: the base change `C_a = R_a[z]/(z^e - u a)` is étale over
`R_a`, and therefore also over `R`.  The hypotheses "`R` Noetherian, `a` a nonzerodivisor, `R/aR`
reduced" of the manuscript are not needed for these two properties.  This is the corresponding
clause of Stacks Example 58.31.4 (Tag `0EYF`) with `f = u a`; it is not tagged because it is
stated through the presentation `R_a[z]/(z^e - u a)` and `C_{ua}` rather than as a morphism of
schemes.

`paper-p.tex` correspondence: Theorem 6.5 (`thm:abhyankar`). -/
theorem standardRing_finite_free_and_etale_away (R : Type u) [CommRing R] (w : Rˣ) (a : R)
    {e : ℕ} (he : 1 ≤ e) (heu : IsUnit (e : R)) :
    Module.Finite R (standardRing R ((w : R) * a) e) ∧
      Module.Free R (standardRing R ((w : R) * a) e) ∧
      Algebra.Etale (Localization.Away a) (AdjoinRoot (localizedStandardPoly w a e)) ∧
      Algebra.Etale R (standardTameRing R ((w : R) * a) e) := by
  have hE : Algebra.Etale (Localization.Away a) (AdjoinRoot (localizedStandardPoly w a e)) :=
    localizedStandardCover_etale w a (by omega) heu
  have hRa : Algebra.Etale R (Localization.Away a) := Algebra.Etale.of_isLocalizationAway a
  have hR : Algebra.Etale R (AdjoinRoot (localizedStandardPoly w a e)) :=
    Algebra.Etale.comp R (Localization.Away a) _
  exact ⟨Pcf.LocalModel.finite_adjoinRoot w a he, Pcf.LocalModel.free_adjoinRoot w a he, hE,
    Algebra.Etale.of_equiv (standardTameRingEquiv w a e).symm⟩

/-- **From the chart to the intrinsic tame condition** (the converse transport of
`isTamelyRamifiedAlongDivisor_of_isTamelyRamifiedInCodimensionOne`, `TameBridge.lean`, whose
isomorphisms are reused here in the opposite direction).  On an affine open `V` on which `D` is
cut out by `a`, if `Frac(R_𝔭) ⊗_R Γ(Y, f⁻¹V)` is tamely ramified with respect to `R_𝔭`, then
`L_ξ` is tamely ramified with respect to `𝒪_{X,ξ}` at the point `ξ = 𝔭`. -/
theorem isTamelyRamifiedOver_genericFiberRing_of_chart {D : X.IdealSheafData}
    {V : X.affineOpens} {a : Γ(X, V)} (hDa : D.ideal V = Ideal.span {a})
    (f : Y ⟶ complementOpen D) [IsFinite f] (p : Ideal Γ(X, V)) [hp : p.IsPrime]
    (H : letI := ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
      IsTamelyRamifiedOver (Localization.AtPrime p)
        (FractionRing (Localization.AtPrime p) ⊗[Γ(X, V)]
          Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1))) :
    IsTamelyRamifiedOver (X.presheaf.stalk (V.2.fromSpec ⟨p, hp⟩))
      (genericFiberRing (complementOpen D) f (V.2.fromSpec ⟨p, hp⟩)) := by
  let _ := ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
  have hgV : IsAffineOpen ((f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    (isAffineOpen_preimage_ι_of_ideal_eq hDa).preimage f
  let pt : PrimeSpectrum Γ(X, V.1) := ⟨p, hp⟩
  let ξ : X := V.2.fromSpec pt
  have hξV : ξ ∈ V.1 := by
    rw [← SetLike.mem_coe, ← V.2.range_fromSpec]
    exact Set.mem_range_self pt
  let xU : V.1 := ⟨ξ, hξV⟩
  have hprime : V.2.primeIdealOf xU = pt :=
    AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec V.2 pt
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk ξ) := X.presheaf.algebra_section_stalk xU
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk ξ) p := by
    have := V.2.isLocalization_stalk xU
    rw [hprime] at this
    exact this
  let e1 : X.presheaf.stalk ξ ≃ₐ[Γ(X, V.1)] Localization.AtPrime p :=
    IsLocalization.algEquiv p.primeCompl _ _
  let O := X.presheaf.stalk ξ
  let K := FractionRing O
  have ht : specFractionFieldToScheme X ξ =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) K)) ≫ V.2.fromSpec := by
    rw [specFractionFieldToScheme, ← V.2.fromSpecStalk_eq_fromSpecStalk hξV]
    change _ ≫ Spec.map (X.presheaf.germ _ ξ hξV) ≫ V.2.fromSpec = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
  have hP := isPullback_tensor_fromSpec (f ≫ (complementOpen D).ι) V.2 hgV K
  rw [← ht] at hP
  let ψ := hP.isoPullback
  have hψ := hP.isoPullback_hom_snd
  let Γψ : Γ(pullback (f ≫ (complementOpen D).ι) (specFractionFieldToScheme X ξ), ⊤) ≅ _ :=
    { hom := ψ.hom.appTop
      inv := ψ.inv.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]; rfl
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]; rfl }
  let E := (Γψ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  have hE : ∀ k : K, E (algebraMap K (genericFiberRing (complementOpen D) f ξ) k) =
      algebraMap K _ k := by
    intro k
    have key : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd (f ≫ (complementOpen D).ι) (specFractionFieldToScheme X ξ)).appTop ≫
          ψ.hom.appTop ≫ (Scheme.ΓSpecIso _).hom = CommRingCat.ofHom (algebraMap K _) := by
      rw [← Category.assoc
          (pullback.snd (f ≫ (complementOpen D).ι) (specFractionFieldToScheme X ξ)).appTop,
        ← Scheme.Hom.comp_appTop, hψ,
        Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    exact congr($key k)
  let M := Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1)
  let E' : genericFiberRing (complementOpen D) f ξ ≃+* K ⊗[Γ(X, V.1)] M := E
  let K' := FractionRing (Localization.AtPrime p)
  let eKr : K ≃+* K' := IsLocalization.ringEquivOfRingEquiv K K' e1.toRingEquiv
    (MulEquivClass.map_nonZeroDivisors e1.toRingEquiv)
  have heKr : ∀ x : O, eKr (algebraMap O K x) =
      algebraMap (Localization.AtPrime p) K' (e1 x) := fun x ↦
    IsLocalization.ringEquivOfRingEquiv_eq _ x
  let eK : K ≃ₐ[Γ(X, V.1)] K' := AlgEquiv.ofRingEquiv (f := eKr) fun r ↦ by
    rw [IsScalarTower.algebraMap_apply Γ(X, V.1) O K, heKr, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  let E2 : K ⊗[Γ(X, V.1)] M ≃+* K' ⊗[Γ(X, V.1)] M :=
    (Algebra.TensorProduct.congr eK (AlgEquiv.refl : M ≃ₐ[Γ(X, V.1)] M)).toRingEquiv
  have hfwd : ∀ x : O, (E'.trans E2) (algebraMap O (genericFiberRing (complementOpen D) f ξ) x) =
      algebraMap (Localization.AtPrime p) (K' ⊗[Γ(X, V.1)] M) (e1 x) := by
    intro x
    change E2 (E (algebraMap K (genericFiberRing (complementOpen D) f ξ)
      (algebraMap O K x))) = _
    rw [hE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    change Algebra.TensorProduct.congr eK AlgEquiv.refl (_ ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp [eK, heKr]
  refine IsTamelyRamifiedOver.of_ringEquiv e1.toRingEquiv.symm (E'.trans E2).symm
    (fun x ↦ ?_) H
  apply (E'.trans E2).injective
  rw [RingEquiv.apply_symm_apply, hfwd]
  congr 1
  exact (e1.apply_symm_apply x).symm

/-- **Characteristic zero: every finite étale cover is tamely ramified in codimension one**
(paper-p, prose after `thm:abhyankar`), in the setting of `thm:abhyankar`: `X` locally Noetherian,
`D ⊂ X` an effective Cartier divisor that is a regular scheme, `f : Y → X ∖ D` finite étale, and
every positive integer invertible on `X` (e.g. `X` a scheme over a field of characteristic `0`).
Then `Y` is tamely ramified over `X` in codimension one (Stacks Section 58.31, `0BSE`).

The regularity of `D` is used only to know that `𝒪_{X,ξ}` is a discrete valuation ring at the
codimension-one points `ξ ∈ D`, which makes the integral closure in `L_ξ` finite; this is the
standing assumption of Stacks Section 58.31 under which tameness in codimension one is defined.

`paper-p.tex` correspondence: Theorem 6.5 (`thm:abhyankar`). -/
theorem isTamelyRamifiedInCodimensionOne_of_isUnit_natCast [IsLocallyNoetherian X]
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Γ(X, ⊤))) :
    IsTamelyRamifiedInCodimensionOne (complementOpen D) f := by
  intro ξ hξ hdim
  have hξD : ξ ∈ D.support := by
    by_contra h
    exact hξ h
  obtain ⟨V, hξV, a, ha, hDa⟩ := hD ξ
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have := isRegularRing_quotient_of_isRegularScheme hDreg hDa
  have hW : IsAffineOpen ((complementOpen D).ι ⁻¹ᵁ V.1) := isAffineOpen_preimage_ι_of_ideal_eq hDa
  have hZV : IsAffineOpen ((f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := hW.preimage f
  let _ : Algebra Γ(X, V) Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1) :=
    ((complementOpen D).ι.app V.1).hom.toAlgebra
  let _ : Algebra Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := (f.app _).hom.toAlgebra
  let _ : Algebra Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
  have : IsScalarTower Γ(X, V) Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change ((f ≫ (complementOpen D).ι).app V.1).hom r =
        (f.app _).hom (((complementOpen D).ι.app V.1).hom r)
      rw [Scheme.Hom.comp_app]; rfl
  have : IsLocalization.Away a Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1) :=
    isLocalization_away_of_ideal_eq hDa
  have : Module.Finite Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := f.finite_app _ hW
  have : Algebra.Etale Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := etale_app_of_etale f hW hZV
  have hnatV : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Γ(X, V)) := fun n hn ↦ by
    simpa only [map_natCast] using
      (hnat n hn).map (X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
  have hchart := AffineTame.isTamelyRamifiedAlongDivisor_of_isUnit_natCast a
    Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
    Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) ha hnatV
  -- the point `ξ` is the prime `𝔭` of the chart
  let xU : V.1 := ⟨ξ, hξV⟩
  let pt := V.2.primeIdealOf xU
  have hξeq : V.2.fromSpec pt = ξ := V.2.fromSpec_primeIdealOf xU
  have hap : a ∈ pt.asIdeal := by
    have := (mem_support_iff_of_ideal_eq hDa hξV).mp hξD
    rwa [mem_basicOpen_iff_notMem_primeIdealOf V.2 a xU, not_not] at this
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk ξ) := X.presheaf.algebra_section_stalk xU
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk ξ) pt.asIdeal :=
    V.2.isLocalization_stalk xU
  let e1 : X.presheaf.stalk ξ ≃ₐ[Γ(X, V.1)] Localization.AtPrime pt.asIdeal :=
    IsLocalization.algEquiv pt.asIdeal.primeCompl _ _
  have hdimp : ringKrullDim (Localization.AtPrime pt.asIdeal) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e1.toRingEquiv]
    exact hdim
  have H := hchart pt.asIdeal inferInstance hap hdimp
  have := isTamelyRamifiedOver_genericFiberRing_of_chart hDa f pt.asIdeal H
  rw [show (⟨pt.asIdeal, inferInstance⟩ : PrimeSpectrum Γ(X, V)) = pt from rfl, hξeq] at this
  exact this

/-- **Abhyankar's lemma in characteristic zero, manuscript form.**  Under the hypotheses of
`thm:abhyankar` with every positive integer invertible on `X`, the tameness hypothesis is
automatic (`isTamelyRamifiedInCodimensionOne_of_isUnit_natCast`) and the normalization has the
displayed étale-local presentation with one equation `a` of `D`.

`paper-p.tex` correspondence: Theorem 6.5 (`thm:abhyankar`). -/
theorem abhyankarLemma_normalization_rootCoverAlong_of_isUnit_natCast [IsLocallyNoetherian X]
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Γ(X, ⊤))) :
    IsEtaleLocallyRootCoverAlong D (f ≫ (complementOpen D).ι).fromNormalization :=
  abhyankarLemma_normalization_rootCoverAlong hD hDreg f
    (isTamelyRamifiedInCodimensionOne_of_isUnit_natCast hD hDreg f hnat)

end Pcf.Stacks.SchemeLevel
