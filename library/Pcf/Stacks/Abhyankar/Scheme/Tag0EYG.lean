/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.ChartFacts
public import Pcf.Stacks.Abhyankar.Scheme.StandardRings
public import Pcf.Stacks.Abhyankar.Scheme.FiniteEtaleSplitting
public import Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame

/-!
# Abhyankar's lemma for a regular divisor, scheme form (Stacks Lemma 58.31.5, Tag `0EYG`)

`Pcf.Stacks.SchemeLevel.abhyankarLemma_scheme`: let `X` be a locally Noetherian scheme, `D ⊂ X` an
effective Cartier divisor such that `D` is a regular scheme, and `Y → X ∖ D` finite étale. If `Y` is
tamely ramified over `X` in codimension one, then étale locally on `X` the morphism `Y → X` is a
finite disjoint union of standard tamely ramified morphisms (Example 58.31.4).

Two forms:
* `abhyankarLemma_scheme_of_abhyankarLemmaTameOver`: with the affine statement as the hypothesis
  `AbhyankarLemmaTameOver X`;
* `abhyankarLemma_scheme`: unconditional, discharging it by the tame affine theorem
  `Pcf.Stacks.abhyankarLemmaTameOfFinite` (any characteristic; on a `ℚ`-scheme the
  characteristic-zero affine theorem is the same tame proof, with tameness supplied by
  `isTamelyRamifiedInCodimensionOneAlong_of_isUnit_natCast`).

## Stacks proof step → Lean

* "for every `x ∈ X` we find an étale neighbourhood `(U, u) → (X, x)`, `U = Spec(A)`, such
  that `Y ×_X U → U` is a finite disjoint union of standard morphisms" →
  `IsEtaleLocallyStandardTame`;
  `exists_etale_pullback_iso_sigma`
* "the case `x ∉ D` follows from Étale Morphisms, Lemma 41.18.3 (`04HN`) with `e = 1`, `f = 1`" →
  `exists_standardTame_of_notMem`, `hasSplitCoverAt_of_finite_etale`, `standardTameRingOneOneEquiv`
* "shrinking `X` we may assume `X = Spec(A)`, `D = V(f)` with `f` a nonzerodivisor; `Y = Spec(B)` is
  affine" → `ChartData.lean`, `hasLocalizedStandardCoverAt_chart`
* "`A/fA` is regular" (`D` regular) → `isRegularRing_quotient_of_isRegularScheme`
* "by Lemma 58.31.1 the base change is tamely ramified in codimension 1" → on the chart:
  `isTamelyRamifiedAlongDivisor_of_isTamelyRamifiedInCodimensionOne`; the base change to `A^{sh}` is
  inside the affine
  statement
* strict henselization, normal domains, root covers, descent along `colim A_λ` → the affine
  statement (`Pcf.Stacks.abhyankarLemmaTameOfFinite`), entering via
  `hasLocalizedStandardCoverAt_of_tame`

Route difference: Stacks proves the affine statement with `B` (the cover itself) as input; the
affine theorem `Pcf.Stacks.abhyankarLemmaTameOfFinite` takes the normalization `S` of `A` in
`B`, assumed finite.
`hasLocalizedStandardCoverAt_of_tame` bridges the two by applying it to the local ring `A_y`,
where the normalization is finite, and
then passing through the strict henselization (`AffineTame.lean`).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Pcf.Stacks.SchemeLevel

variable {X Y : Scheme.{u}} {D : X.IdealSheafData}

/-- The étale-local standard tame structure at a point `x ∈ D`. -/
theorem exists_standardTame_of_mem [IsLocallyNoetherian X] (hA : AbhyankarLemmaTameOver X)
    (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) (x : X) (hxD : x ∈ D.support) :
    ∃ (A : CommRingCat.{u}) (φ : Spec A ⟶ X), Etale φ ∧ x ∈ Set.range φ.base ∧
    ∃ (n : ℕ) (fs : Fin n → A) (e : Fin n → ℕ), (∀ i, IsStandardTameData A (fs i) (e i)) ∧
      ∃ ψ : pullback (f ≫ (complementOpen D).ι) φ ≅
          ∐ (fun i ↦ Spec (CommRingCat.of (standardTameRing A (fs i) (e i)))),
        ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
          (algebraMap A (standardTameRing A (fs i) (e i))))) =
          pullback.snd (f ≫ (complementOpen D).ι) φ := by
  obtain ⟨V, hxV, a, ha, hDa⟩ := hD x
  have hW : IsAffineOpen ((complementOpen D).ι ⁻¹ᵁ V.1) := isAffineOpen_preimage_ι_of_ideal_eq hDa
  have hZV : IsAffineOpen ((f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := hW.preimage f
  let _ : Algebra Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
  have hy : a ∈ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    have := (mem_support_iff_of_ideal_eq hDa hxV).mp hxD
    rwa [mem_basicOpen_iff_notMem_primeIdealOf V.2 a ⟨x, hxV⟩, not_not] at this
  obtain ⟨A, _, _, hAet, hy', hAN, haA, hregA, n, e, u, he, heu, ⟨g⟩⟩ :=
    hasLocalizedStandardCoverAt_chart hA hDreg f htame ha hDa _ hy
  let g' := g.trans (AlgEquiv.piCongrRight fun i ↦
    (standardTameRingEquiv (u i) (algebraMap Γ(X, V) A a) (e i)).symm)
  obtain ⟨φ, hφ, hxφ, ψ, hψ⟩ := exists_etale_pullback_iso_sigma (f ≫ (complementOpen D).ι)
    V.2 hZV hxV A hy' (fun i ↦ standardTameRing A ((u i : A) * algebraMap Γ(X, V) A a) (e i)) g'
  have hred : IsReduced (A ⧸ Ideal.span {algebraMap Γ(X, V) A a}) := isReduced_of_isRegularRing
  exact ⟨CommRingCat.of A, φ, hφ, hxφ, n, fun i ↦ (u i : A) * algebraMap Γ(X, V) A a, e,
    fun i ↦ isStandardTameData_unit_mul (u i) haA hred (he i) (heu i), ψ, hψ⟩

/-- The étale-local standard tame structure at a point `x ∉ D`: Stacks' "Étale Morphisms,
Lemma 41.18.3 (Tag `04HN`) and `e = 1`, `f = 1`". -/
theorem exists_standardTame_of_notMem [IsLocallyNoetherian X]
    (hD : IsEffectiveCartier D)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f] (x : X) (hxD : x ∉ D.support) :
    ∃ (A : CommRingCat.{u}) (φ : Spec A ⟶ X), Etale φ ∧ x ∈ Set.range φ.base ∧
    ∃ (n : ℕ) (fs : Fin n → A) (e : Fin n → ℕ), (∀ i, IsStandardTameData A (fs i) (e i)) ∧
      ∃ ψ : pullback (f ≫ (complementOpen D).ι) φ ≅
          ∐ (fun i ↦ Spec (CommRingCat.of (standardTameRing A (fs i) (e i)))),
        ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
          (algebraMap A (standardTameRing A (fs i) (e i))))) =
          pullback.snd (f ≫ (complementOpen D).ι) φ := by
  obtain ⟨V, hxV, hVU⟩ := exists_affine_le_complement hD hxD
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨hZV, hfin, het⟩ := finite_etale_of_le f hVU
  let _ : Algebra Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
  obtain ⟨A, _, _, hAet, hy', hAN, n, ⟨g⟩⟩ :=
    hasSplitCoverAt_of_finite_etale Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1)
      (V.2.primeIdealOf ⟨x, hxV⟩)
  let g' := g.trans (AlgEquiv.piCongrRight fun _ ↦
    (standardTameRingOneOneEquiv (A := A)).symm)
  obtain ⟨φ, hφ, hxφ, ψ, hψ⟩ := exists_etale_pullback_iso_sigma (f ≫ (complementOpen D).ι)
    V.2 hZV hxV A hy' (fun _ : Fin n ↦ standardTameRing A 1 1) g'
  exact ⟨CommRingCat.of A, φ, hφ, hxφ, n, fun _ ↦ 1, fun _ ↦ 1,
    fun _ ↦ isStandardTameData_one_one, ψ, hψ⟩

/-- **Stacks Lemma 58.31.5 (Tag `0EYG`), with the affine statement as a hypothesis.**  See
`abhyankarLemma_scheme` for the unconditional form. -/
theorem abhyankarLemma_scheme_of_abhyankarLemmaTameOver (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hA : AbhyankarLemmaTameOver X)
    (D : X.IdealSheafData) (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    IsEtaleLocallyStandardTame (f ≫ (complementOpen D).ι) := by
  intro x
  by_cases hxD : x ∈ D.support
  · exact exists_standardTame_of_mem hA hD hDreg f htame x hxD
  · exact exists_standardTame_of_notMem hD f x hxD

/-- **Abhyankar's lemma for a regular divisor (Stacks Lemma 58.31.5, Tag `0EYG`).**

Let `X` be a locally Noetherian scheme.  Let `D ⊂ X` be an effective Cartier divisor such that
`D` is a regular scheme.  Let `Y → X ∖ D` be a finite étale morphism.  If `Y` is tamely ramified
over `X` in codimension `1`, then étale locally on `X` the morphism `Y → X` is a finite disjoint
union of standard tamely ramified morphisms as described in Example 58.31.4.

Proof: `abhyankarLemma_scheme_of_abhyankarLemmaTameOver`, with the affine statement supplied by
`Pcf.Stacks.abhyankarLemmaTameOfFinite`.

`paper-p.tex` correspondence: Theorem 6.5 (`thm:abhyankar`). -/
@[stacks 0EYG]
theorem abhyankarLemma_scheme (X : Scheme.{u}) [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    IsEtaleLocallyStandardTame (f ≫ (complementOpen D).ι) :=
  abhyankarLemma_scheme_of_abhyankarLemmaTameOver X
    (abhyankarLemmaTameOver_of_forall X Pcf.Stacks.abhyankarLemmaTameOfFinite)
    D hD hDreg f htame

end Pcf.Stacks.SchemeLevel
