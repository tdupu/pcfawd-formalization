/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Tag0EYG
public import Pcf.Stacks.Abhyankar.Scheme.AffineNormalization
public import Pcf.Stacks.Abhyankar.Scheme.NormalizationChart
public import Pcf.Stacks.Abhyankar.Scheme.ReducedPreimage
public import Pcf.Stacks.Abhyankar.Scheme.LocalOnTarget

/-!
# The normalization addendum (Stacks Lemma 58.31.6, Tag `0EYH`)

`Pcf.Stacks.SchemeLevel.abhyankarLemma_normalization`: in the situation of `0EYG`, the normalization
`π : Y' → X` of `X` in `Y` (Mathlib's `Scheme.Hom.normalization` of `Y → X ∖ D ⊂ X`) is finite
locally free (stated as finite, flat and locally of finite presentation, which is equivalent by
Morphisms, Lemma 29.49.2, Tag `02KB`), with
1. `π⁻¹(X ∖ D) ≅ Y` over `X ∖ D`,
2. `D' = π⁻¹(D)_red = (D.comap π).radical` an effective Cartier divisor on `Y'`,
3. `D'` a regular scheme,

and étale locally on `X`, `Y' → X` is a finite disjoint union of `Spec(A[x]/(x^e - f)) → Spec(A)`
with `A` Noetherian, `f` a nonzerodivisor with `A/fA` regular, `e ≥ 1` invertible in `A`.

Forms: `abhyankarLemma_normalization_of_abhyankarLemmaTameOver` (affine statement as hypothesis), `abhyankarLemma_normalization` (unconditional, via
`Pcf.Stacks.abhyankarLemmaTameOfFinite`), `abhyankarLemma_normalization_of_isUnit_natCast` (on a `ℚ`-scheme, via the
characteristic-zero `Pcf.Stacks.abhyankarLemmaOfFinite`).

## Stacks proof step → Lean

* "taking the normalization of `X` in `Y` commutes with étale base change (More on Morphisms, Lemma
  37.19.2)" → affine form: `nonempty_baseChange_integralClosure_algEquiv` (via pcf's
  `smoothBaseChange_isIntegralClosure_localizationAway`, Tag `03GV`); on charts
  `normalizationAppAlgEquiv`
* "we may prove the statements on the local structure étale locally on `X`; by `0EYG` we may assume
  `X = Spec(A)` … `Y` a finite disjoint union of `A_f[x]/(x^e - f)`" →
  `hasLocalizedStandardCoverAt_chart`, `normalization_appTop_algEquiv_standardCovers_of_chart`
* "the integral closure of `A` in `A_f[x]/(x^e - f)` is `A[x]/(x^e - f)` (localizations at primes
  over `(f)` are regular); details omitted" → pcf's
  `normalizationEquivStandardCoversOfLocalizedPresentation` (characteristic-zero development)
* finite locally free → `integralClosure_finite`, `integralClosure_flat` (faithfully flat descent
  along an étale cover), `isFinite_of_iSup_eq_top`, `flat_of_iSup_eq_top`
* (1) restriction to `X ∖ D` → `exists_iso_normalization_restrict` (Mathlib `normalizationPullback`,
  Tag `03GV`, along the open immersion)
* (2), (3) → `exists_radical_eq_span_of_mem`, `isRegularRing_quotient_radical` (descent of
  principality and regularity along étale maps), assembled by `isEffectiveCartier_radical_comap`,
  `isRegularScheme_radical_comap`

Route differences: Stacks deduces every assertion étale locally and leaves the descent implicit;
here the étale-local facts are descended explicitly on affine charts (finiteness and flatness by
faithfully flat descent; principality of `√(a)` and regularity of `N/√(a)` along flat local
unramified maps; see `AffineNormalization.lean`).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Pcf.Stacks.SchemeLevel

variable {X Y : Scheme.{u}} {D : X.IdealSheafData}

/-- The zero ring is regular. -/
theorem isRegularRing_of_subsingleton (A : Type*) [CommRing A] [Subsingleton A] :
    IsRegularRing A := by
  have : IsNoetherianRing A := inferInstance
  refine isRegularRing_iff.mpr fun p hp ↦ ?_
  exact absurd (Subsingleton.elim (1 : A) 0) (fun h ↦ hp.ne_top (Ideal.eq_top_of_isUnit_mem _
    (h ▸ p.zero_mem) isUnit_one |>.symm ▸ rfl) |>.elim)

/-- Chart-level algebra for `0EYH` on an affine open `V` with `D ∩ V = V(a)`, for the
normalization `π : Y' → X` of `X` in `Y`. -/
theorem normalization_appTop_algEquiv_standardCovers_of_chart [IsLocallyNoetherian X] (hA : AbhyankarLemmaTameOver X)
    (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) {V : X.affineOpens} {a : Γ(X, V)}
    (ha : a ∈ nonZeroDivisors Γ(X, V)) (hDa : D.ideal V = Ideal.span {a}) :
    letI := ((f ≫ (complementOpen D).ι).fromNormalization.app V.1).hom.toAlgebra
    ((f ≫ (complementOpen D).ι).fromNormalization.app V.1).hom.Finite ∧
    ((f ≫ (complementOpen D).ι).fromNormalization.app V.1).hom.Flat ∧
    (∀ Q : PrimeSpectrum Γ((f ≫ (complementOpen D).ι).normalization,
        (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1),
      (f ≫ (complementOpen D).ι).fromNormalization.app V.1 a ∈ Q.asIdeal →
      ∃ g, g ∉ Q.asIdeal ∧
        ∃ t : Γ((f ≫ (complementOpen D).ι).normalization,
            ((f ≫ (complementOpen D).ι).normalization).basicOpen g),
          t ∈ nonZeroDivisors _ ∧
          (Ideal.span (singleton (((f ≫ (complementOpen D).ι).normalization).presheaf.map
            (homOfLE (Scheme.basicOpen_le _ g)).op
              ((f ≫ (complementOpen D).ι).fromNormalization.app V.1 a)))).radical =
            Ideal.span {t}) ∧
    IsRegularRing (Γ((f ≫ (complementOpen D).ι).normalization,
        (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) ⧸
      (Ideal.span {(f ≫ (complementOpen D).ι).fromNormalization.app V.1 a}).radical) ∧
    (∀ y : PrimeSpectrum Γ(X, V), a ∈ y.asIdeal →
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra Γ(X, V) A), Algebra.Etale Γ(X, V) A ∧
        (∃ y' : PrimeSpectrum A, y'.asIdeal.under Γ(X, V) = y.asIdeal) ∧ IsNoetherianRing A ∧
        algebraMap Γ(X, V) A a ∈ nonZeroDivisors A ∧
        IsRegularRing (A ⧸ Ideal.span {algebraMap Γ(X, V) A a}) ∧
        ∃ (n : ℕ) (e : Fin n → ℕ) (u : Fin n → Aˣ), (∀ i, 1 ≤ e i) ∧ (∀ i, IsUnit (e i : A)) ∧
          Nonempty (A ⊗[Γ(X, V)] Γ((f ≫ (complementOpen D).ι).normalization,
              (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) ≃ₐ[A]
            ∀ i, standardRing A ((u i : A) * algebraMap Γ(X, V) A a) (e i))) := by
  let _ : Algebra Γ(X, V) Γ((f ≫ (complementOpen D).ι).normalization,
      (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).fromNormalization.app V.1).hom.toAlgebra
  have hloc := hasLocalizedStandardCoverAt_chart hA hDreg f htame ha hDa
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
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := finite_app_of_isFinite f hW
  have : Algebra.Etale Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := etale_app_of_etale f hW hZV
  let E := normalizationAppAlgEquiv (f ≫ (complementOpen D).ι) V.2
  have hEa : E ((f ≫ (complementOpen D).ι).fromNormalization.app V.1 a) =
      algebraMap Γ(X, V) _ a := E.commutes a
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := integralClosure_finite a Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) ha hloc
    change Module.Finite Γ(X, V) _
    exact Module.Finite.equiv E.symm.toLinearEquiv
  · have := integralClosure_flat a Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) ha hloc
    change Module.Flat Γ(X, V) _
    exact Module.Flat.of_linearEquiv E.toLinearEquiv
  · intro Q hQ
    obtain ⟨h, hhQ, hNh⟩ := exists_radical_eq_span_of_mem a
      Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) ha hloc
      (Q.comap E.symm.toRingEquiv.toRingHom) (by
        change E.symm (algebraMap Γ(X, V) _ a) ∈ Q.asIdeal
        rw [← hEa, AlgEquiv.symm_apply_apply]; exact hQ)
    refine ⟨E.symm h, hhQ, ?_⟩
    have hpre : IsAffineOpen ((f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
      V.2.preimage _
    let g := E.symm h
    let _ : Algebra Γ((f ≫ (complementOpen D).ι).normalization,
        (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1)
        Γ((f ≫ (complementOpen D).ι).normalization,
          ((f ≫ (complementOpen D).ι).normalization).basicOpen g) :=
      (((f ≫ (complementOpen D).ι).normalization).presheaf.map
        (homOfLE (Scheme.basicOpen_le _ g)).op).hom.toAlgebra
    have hloc' : IsLocalization.Away g Γ((f ≫ (complementOpen D).ι).normalization,
        ((f ≫ (complementOpen D).ι).normalization).basicOpen g) :=
      hpre.isLocalization_basicOpen g
    let _ : Algebra (integralClosure Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1))
        Γ((f ≫ (complementOpen D).ι).normalization,
          ((f ≫ (complementOpen D).ι).normalization).basicOpen g) :=
      ((algebraMap _ _).comp E.symm.toRingEquiv.toRingHom).toAlgebra
    have : IsLocalization.Away h Γ((f ≫ (complementOpen D).ι).normalization,
        ((f ≫ (complementOpen D).ι).normalization).basicOpen g) := by
      have := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers g)
        Γ((f ≫ (complementOpen D).ι).normalization,
          ((f ≫ (complementOpen D).ι).normalization).basicOpen g) E.toRingEquiv
      rw [Submonoid.map_powers] at this
      have hg : E.toRingEquiv g = h := E.apply_symm_apply h
      rw [hg] at this
      exact this
    obtain ⟨t, ht, hrad⟩ := hNh Γ((f ≫ (complementOpen D).ι).normalization,
      ((f ≫ (complementOpen D).ι).normalization).basicOpen g)
    refine ⟨t, ht, ?_⟩
    rw [← hrad]
    congr 3
    change _ = (((f ≫ (complementOpen D).ι).normalization).presheaf.map
      (homOfLE (Scheme.basicOpen_le _ g)).op).hom (E.symm (algebraMap Γ(X, V) _ a))
    rw [← hEa, AlgEquiv.symm_apply_apply]
  · have hreg := isRegularRing_quotient_radical a
      Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) ha hloc
    refine IsRegularRing.of_ringEquiv (Ideal.quotientEquiv
      (Ideal.span (singleton ((f ≫ (complementOpen D).ι).fromNormalization.app V.1 a))).radical
      (Ideal.span (singleton (algebraMap Γ(X, V)
        (integralClosure Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1)) a))).radical
      E.toRingEquiv ?_).symm
    rw [show (E.toRingEquiv : _ →+* _) = E.toRingEquiv.toRingHom from rfl,
      Ideal.map_radical_of_surjective (f := E.toRingEquiv.toRingHom) E.surjective, Ideal.map_span,
      Set.image_singleton]
    · change _ = (Ideal.span
        (singleton (E ((f ≫ (complementOpen D).ι).fromNormalization.app V.1 a)))).radical
      rw [hEa]
    · intro x hx
      have : x = 0 := E.injective ((RingHom.mem_ker.mp hx).trans (map_zero E).symm)
      rw [this]; exact Ideal.zero_mem _
  · intro y hy
    obtain ⟨A, _, _, hAet, hy', hAN, haA, hregA, n, e, u, he, heu, ⟨g⟩⟩ := hloc y hy
    obtain ⟨gN⟩ := nonempty_baseChange_integralClosure_algEquiv a
      Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) haA e u he g
    refine ⟨A, inferInstance, inferInstance, hAet, hy', hAN, haA, hregA, n, e, u, he, heu, ⟨?_⟩⟩
    let F := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[Γ(X, V)] A) E
    exact (AlgEquiv.ofRingEquiv (f := F.toRingEquiv) (fun x ↦ by
        change F (x ⊗ₜ 1) = x ⊗ₜ 1
        simp only [F, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
        rfl)).trans gN

/-- The étale-local root-cover structure of the normalization at a point `x ∉ D`. -/
theorem exists_rootCover_of_notMem [IsLocallyNoetherian X] (hD : IsEffectiveCartier D)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f] (x : X) (hxD : x ∉ D.support) :
    ∃ (A : CommRingCat.{u}) (φ : Spec A ⟶ X), Etale φ ∧ x ∈ Set.range φ.base ∧
      IsNoetherianRing A ∧
      ∃ (n : ℕ) (fs : Fin n → A) (e : Fin n → ℕ),
        (∀ i, fs i ∈ nonZeroDivisors A ∧ IsRegularRing (A ⧸ Ideal.span {fs i}) ∧ 1 ≤ e i ∧
          IsUnit (e i : A)) ∧
        ∃ ψ : pullback (f ≫ (complementOpen D).ι).fromNormalization φ ≅
            ∐ (fun i ↦ Spec (CommRingCat.of (standardRing A (fs i) (e i)))),
          ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
            (algebraMap A (standardRing A (fs i) (e i))))) =
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
  -- the normalization is `Γ(Y, f⁻¹V)` itself, which is integral over `Γ(X, V)`
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
    (standardRingOneOneEquiv (A := A)).symm)
  obtain ⟨φ, hφ, hxφ, ψ, hψ⟩ := exists_etale_pullback_iso_sigma
    (f ≫ (complementOpen D).ι).fromNormalization V.2 hpre hxV A hy'
    (fun _ : Fin n ↦ standardRing A 1 1) g'
  refine ⟨CommRingCat.of A, φ, hφ, hxφ, hAN, n, fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ ⟨one_mem _, ?_,
    le_rfl, by simp⟩, ψ, hψ⟩
  have : Subsingleton (A ⧸ Ideal.span {(1 : A)}) := by
    rw [Ideal.span_singleton_one]; infer_instance
  exact isRegularRing_of_subsingleton _

/-- The étale-local root-cover structure of the normalization at a point `x ∈ D`. -/
theorem exists_rootCover_of_mem [IsLocallyNoetherian X] (hA : AbhyankarLemmaTameOver X)
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) (x : X) (hxD : x ∈ D.support) :
    ∃ (A : CommRingCat.{u}) (φ : Spec A ⟶ X), Etale φ ∧ x ∈ Set.range φ.base ∧
      IsNoetherianRing A ∧
      ∃ (n : ℕ) (fs : Fin n → A) (e : Fin n → ℕ),
        (∀ i, fs i ∈ nonZeroDivisors A ∧ IsRegularRing (A ⧸ Ideal.span {fs i}) ∧ 1 ≤ e i ∧
          IsUnit (e i : A)) ∧
        ∃ ψ : pullback (f ≫ (complementOpen D).ι).fromNormalization φ ≅
            ∐ (fun i ↦ Spec (CommRingCat.of (standardRing A (fs i) (e i)))),
          ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
            (algebraMap A (standardRing A (fs i) (e i))))) =
            pullback.snd (f ≫ (complementOpen D).ι).fromNormalization φ := by
  obtain ⟨V, hxV, a, ha, hDa⟩ := hD x
  have hpre : IsAffineOpen ((f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
    V.2.preimage _
  have hy : a ∈ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    have := (mem_support_iff_of_ideal_eq hDa hxV).mp hxD
    rwa [mem_basicOpen_iff_notMem_primeIdealOf V.2 a ⟨x, hxV⟩, not_not] at this
  obtain ⟨-, -, -, -, hstr⟩ := normalization_appTop_algEquiv_standardCovers_of_chart hA hDreg f htame ha hDa
  let _ : Algebra Γ(X, V) Γ((f ≫ (complementOpen D).ι).normalization,
      (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).fromNormalization.app V.1).hom.toAlgebra
  obtain ⟨A, _, _, hAet, hy', hAN, haA, hregA, n, e, u, he, heu, ⟨g⟩⟩ := hstr _ hy
  obtain ⟨φ, hφ, hxφ, ψ, hψ⟩ := exists_etale_pullback_iso_sigma
    (f ≫ (complementOpen D).ι).fromNormalization V.2 hpre hxV A hy'
    (fun i ↦ standardRing A ((u i : A) * algebraMap Γ(X, V) A a) (e i)) g
  refine ⟨CommRingCat.of A, φ, hφ, hxφ, hAN, n, fun i ↦ (u i : A) * algebraMap Γ(X, V) A a, e,
    fun i ↦ ⟨mul_mem (Units.isUnit (u i)).mem_nonZeroDivisors haA, ?_, he i, heu i⟩, ψ, hψ⟩
  rw [Ideal.span_singleton_mul_left_unit (Units.isUnit (u i))]
  exact hregA

/-- **Stacks Lemma 58.31.6 (Tag `0EYH`), with the affine statement as a hypothesis.**  See
`abhyankarLemma_normalization` for the unconditional form. -/
theorem abhyankarLemma_normalization_of_abhyankarLemmaTameOver (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hA : AbhyankarLemmaTameOver X)
    (D : X.IdealSheafData) (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    let π := (f ≫ (complementOpen D).ι).fromNormalization
    (IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π) ∧
    (∃ e : Y ≅ (π ⁻¹ᵁ complementOpen D).toScheme, e.hom ≫ (π ∣_ complementOpen D) = f) ∧
    IsEffectiveCartier (D.comap π).radical ∧
    IsRegularScheme (D.comap π).radical.subscheme ∧
    IsEtaleLocallyStandardRootCover π := by
  intro π
  choose V hxV a ha hDa using hD
  have hcover : ⨆ x, ((V x : X.affineOpens) : X.Opens) = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  have hpre : ∀ x, IsAffineOpen (π ⁻¹ᵁ (V x : X.Opens)) := fun x ↦ (V x).2.preimage π
  have hD' : IsEffectiveCartier D := fun x ↦ ⟨V x, hxV x, a x, ha x, hDa x⟩
  have hfin : IsFinite π := isFinite_of_iSup_eq_top π V hcover hpre fun x ↦
    (normalization_appTop_algEquiv_standardCovers_of_chart hA hDreg f htame (ha x) (hDa x)).1
  refine ⟨⟨hfin, flat_of_iSup_eq_top π V hcover hpre fun x ↦
      (normalization_appTop_algEquiv_standardCovers_of_chart hA hDreg f htame (ha x) (hDa x)).2.1,
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance⟩,
    exists_iso_normalization_restrict _ f, ?_, ?_, ?_⟩
  · exact isEffectiveCartier_radical_comap π hD' fun W b hb hDb Q hQ ↦
      (normalization_appTop_algEquiv_standardCovers_of_chart hA hDreg f htame hb hDb).2.2.1 Q hQ
  · exact isRegularScheme_radical_comap π hD' fun W b hb hDb ↦
      (normalization_appTop_algEquiv_standardCovers_of_chart hA hDreg f htame hb hDb).2.2.2.1
  · intro x
    by_cases hxD : x ∈ D.support
    · exact exists_rootCover_of_mem hA hD' hDreg f htame x hxD
    · exact exists_rootCover_of_notMem hD' f x hxD

/-- **The normalization addendum to Abhyankar's lemma (Stacks Lemma 58.31.6, Tag `0EYH`).**

In the situation of Lemma 58.31.5 (`abhyankarLemma_scheme`) the normalization of `X` in `Y` is a finite
locally free morphism `π : Y' → X` (here: finite, flat and locally of finite presentation, which
is "finite locally free" by Tag `02KB`) such that
1. the restriction of `Y'` to `X ∖ D` is isomorphic to `Y`,
2. `D' = π⁻¹(D)_red` is an effective Cartier divisor on `Y'`, and
3. `D'` is a regular scheme.

Moreover, étale locally on `X` the morphism `Y' → X` is a finite disjoint union of morphisms
`Spec(A[x]/(x^e - f)) → Spec(A)` where `A` is a Noetherian ring, `f ∈ A` is a nonzerodivisor
with `A/fA` regular, and `e ≥ 1` is invertible in `A`.

Proof: `abhyankarLemma_normalization_of_abhyankarLemmaTameOver` with the affine statement from
`Pcf.Stacks.abhyankarLemmaTameOfFinite`. -/
@[stacks 0EYH "finite locally free stated as finite + flat + locally of finite presentation \
    (02KB)"]
theorem abhyankarLemma_normalization (X : Scheme.{u}) [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    let π := (f ≫ (complementOpen D).ι).fromNormalization
    (IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π) ∧
    (∃ e : Y ≅ (π ⁻¹ᵁ complementOpen D).toScheme, e.hom ≫ (π ∣_ complementOpen D) = f) ∧
    IsEffectiveCartier (D.comap π).radical ∧
    IsRegularScheme (D.comap π).radical.subscheme ∧
    IsEtaleLocallyStandardRootCover π :=
  abhyankarLemma_normalization_of_abhyankarLemmaTameOver X
    (abhyankarLemmaTameOver_of_forall X Pcf.Stacks.abhyankarLemmaTameOfFinite)
    D hD hDreg f htame

/-- **Stacks Tag `0EYH` on a `ℚ`-scheme, characteristic-zero proof** (from
`Pcf.Stacks.abhyankarLemmaOfFinite`, without the tame theorem). -/
@[stacks 0EYH "every positive integer invertible on X; proof via the characteristic-zero affine \
    theorem; finite locally free stated as finite + flat + locally of finite presentation (02KB)"]
theorem abhyankarLemma_normalization_of_isUnit_natCast (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : Γ(X, ⊤)))
    (D : X.IdealSheafData) (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    let π := (f ≫ (complementOpen D).ι).fromNormalization
    (IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π) ∧
    (∃ e : Y ≅ (π ⁻¹ᵁ complementOpen D).toScheme, e.hom ≫ (π ∣_ complementOpen D) = f) ∧
    IsEffectiveCartier (D.comap π).radical ∧
    IsRegularScheme (D.comap π).radical.subscheme ∧
    IsEtaleLocallyStandardRootCover π :=
  abhyankarLemma_normalization_of_abhyankarLemmaTameOver X (abhyankarLemmaTameOver_of_isUnit_natCast X hnat) D hD hDreg f htame

end Pcf.Stacks.SchemeLevel
