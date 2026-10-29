/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Tag0EYH
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Abhyankar's lemma in the form stated in `paper.tex`

`paper.tex`, Theorem `thm:abhyankar` and the "Explicitly" paragraph after it.
Its hypotheses are those of `Pcf.Stacks.SchemeLevel.abhyankarLemma_normalization`
(Stacks `0EYG` + `0EYH`). The conclusion `IsEtaleLocallyStandardRootCover` of that
theorem forgets the relation between the local equations of the components and
the divisor `D`. Here that relation is recorded: every point of `U` lies in the
image of an étale `φ : Spec R → U`, with `R` Noetherian and a single
nonzerodivisor `a ∈ R`, such that

* `D ×_U Spec R ≅ Spec (R/aR)` over `Spec R`, equivalently `φ*D` is the ideal
  sheaf of `Spec (R/aR) → Spec R`;
* `R/aR` is regular;
* `V ×_U Spec R ≅ ∐_i Spec R[z]/(z^{e_i} - u_i a)` over `Spec R`, with
  `u_i ∈ Rˣ` and `e_i ≥ 1` invertible in `R`.

At points outside `D` the chart misses `D` and `a = 1`, `u_i = 1`, `e_i = 1`
(so `D ×_U Spec R = V(1) = ∅`); this is the manuscript's statement with `a` a
unit.

The proof re-runs the chart arguments of `exists_rootCover_of_mem` and
`exists_rootCover_of_notMem` (whose statements drop `a` and `u_i`), using
`normalization_appTop_algEquiv_standardCovers_of_chart` and
`exists_pullback_iso_sigma` directly, so that the étale map `φ` is the explicit
`Spec R → Spec Γ(X, V) ≅ V ⊂ X`. The identification of `D ×_U Spec R` is the
base change of the affine piece `Spec (Γ(V)/D(V)) → Spec Γ(V)` of `D`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct Pcf.Stacks.SchemeLevel

namespace Pcf.PaperCharZero

variable {X : Scheme.{u}}

/-- `Γ(D, D ∩ V) ≅ Γ(X, V)/D(V)` as `Γ(X, V)`-algebras, the algebra structure on the
left being the restriction map of the closed immersion. -/
noncomputable def subschemeAppAlgEquiv (D : X.IdealSheafData) (V : X.affineOpens) :
    letI := (D.subschemeι.app V.1).hom.toAlgebra
    Γ(D.subscheme, D.subschemeι ⁻¹ᵁ V.1) ≃ₐ[Γ(X, V)] Γ(X, V) ⧸ D.ideal V :=
  letI := (D.subschemeι.app V.1).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := (D.subschemeObjIso V).commRingCatIsoToRingEquiv) fun r => by
    change (D.subschemeObjIso V).hom.hom ((D.subschemeι.app V.1).hom r) = _
    rw [D.subschemeι_app V]
    change ((D.subschemeObjIso V).inv ≫ (D.subschemeObjIso V).hom).hom _ = _
    rw [Iso.inv_hom_id]
    rfl

/-- **The divisor after an affine étale-chart base change.** If `D` is cut out by
`a` on the affine open `V` and `A` is a `Γ(X, V)`-algebra, then over `Spec A` the
base change of `D` along `Spec A → Spec Γ(V) ≅ V ⊂ X` is `Spec (A/aA)`. -/
theorem exists_pullback_subschemeι_iso (D : X.IdealSheafData) {V : X.affineOpens}
    {a : Γ(X, V)} (hDa : D.ideal V = Ideal.span {a}) (A : Type u) [CommRing A]
    [Algebra Γ(X, V) A] :
    ∃ χ : pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ V.2.fromSpec)
        D.subschemeι ≅ Spec (CommRingCat.of (A ⧸ Ideal.span {algebraMap Γ(X, V) A a})),
      χ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = pullback.fst _ _ := by
  let _ := (D.subschemeι.app V.1).hom.toAlgebra
  have hZV : IsAffineOpen (D.subschemeι ⁻¹ᵁ V.1) := V.2.preimage _
  have hP := (isPullback_tensor_fromSpec D.subschemeι V.2 hZV A).flip
  let e1 := subschemeAppAlgEquiv D V
  let F := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[Γ(X, V)] A) e1
  let F' : A ⊗[Γ(X, V)] Γ(D.subscheme, D.subschemeι ⁻¹ᵁ V.1) ≃ₐ[A]
      A ⊗[Γ(X, V)] (Γ(X, V) ⧸ D.ideal V) :=
    AlgEquiv.ofRingEquiv (f := F.toRingEquiv) fun x ↦ by
      change F (x ⊗ₜ 1) = x ⊗ₜ 1
      simp only [F, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
      rfl
  have hmap : (D.ideal V).map (algebraMap Γ(X, V) A) =
      Ideal.span {algebraMap Γ(X, V) A a} := by
    rw [hDa, Ideal.map_span, Set.image_singleton]
  let G : A ⊗[Γ(X, V)] Γ(D.subscheme, D.subschemeι ⁻¹ᵁ V.1) ≃ₐ[A]
      A ⧸ Ideal.span {algebraMap Γ(X, V) A a} :=
    (F'.trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (D.ideal V)).symm).trans
      (Ideal.quotientEquivAlgOfEq A hmap)
  let Gi : CommRingCat.of (A ⧸ Ideal.span {algebraMap Γ(X, V) A a}) ⟶
      CommRingCat.of (A ⊗[Γ(X, V)] Γ(D.subscheme, D.subschemeι ⁻¹ᵁ V.1)) :=
    CommRingCat.ofHom G.symm.toRingEquiv.toRingHom
  have : IsIso Gi := by
    refine ⟨CommRingCat.ofHom G.toRingEquiv.toRingHom, ?_, ?_⟩ <;> ext x <;> simp [Gi]
  refine ⟨hP.isoPullback.symm ≪≫ asIso (Spec.map Gi), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, ← Spec.map_comp]
  have hG : CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap Γ(X, V) A a})) ≫ Gi =
      CommRingCat.ofHom (algebraMap A
        (A ⊗[Γ(X, V)] Γ(D.subscheme, D.subschemeι ⁻¹ᵁ V.1))) := by
    ext x
    change G.symm (algebraMap A _ x) = _
    exact G.symm.commutes x
  rw [hG, IsPullback.isoPullback_inv_fst]

/-- The explicit étale chart `Spec A → Spec Γ(V) ≅ V ⊂ X` is étale and hits `x`. -/
theorem chart_etale_mem_range {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hx : x ∈ V)
    (A : Type u) [CommRing A] [Algebra Γ(X, V) A] [Algebra.Etale Γ(X, V) A]
    (hy : ∃ y' : PrimeSpectrum A, y'.asIdeal.under Γ(X, V) = (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec) ∧
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec) := by
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

/-- The local conclusion of `thm:abhyankar` at one point, in the manuscript's form. -/
def IsAbhyankarChartAt (D : X.IdealSheafData) {V : Scheme.{u}} (π : V ⟶ X) (x : X) : Prop :=
  ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ X), Etale φ ∧ x ∈ Set.range φ ∧ IsNoetherianRing R ∧
    ∃ a : R, a ∈ nonZeroDivisors R ∧ IsRegularRing (R ⧸ Ideal.span {a}) ∧
      (∃ χ : pullback φ D.subschemeι ≅ Spec (CommRingCat.of (R ⧸ Ideal.span {a})),
        χ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = pullback.fst _ _) ∧
      ∃ (n : ℕ) (e : Fin n → ℕ) (u : Fin n → Rˣ), (∀ i, 1 ≤ e i ∧ IsUnit (e i : R)) ∧
        ∃ ψ : pullback π φ ≅
            ∐ (fun i ↦ Spec (CommRingCat.of (standardRing R ((u i : R) * a) (e i)))),
          ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
            (algebraMap R (standardRing R ((u i : R) * a) (e i))))) = pullback.snd π φ

/-- The chart at a point of `D`. -/
theorem isAbhyankarChartAt_of_mem [IsLocallyNoetherian X] (hA : AbhyankarLemmaTameOver X)
    {D : X.IdealSheafData} (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) (x : X)
    (hxD : x ∈ D.support) :
    IsAbhyankarChartAt D (f ≫ (complementOpen D).ι).fromNormalization x := by
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
  obtain ⟨A, _, _, hAet, hy', hAN, haA, hregA, n, e, u, he, heu, ⟨g⟩⟩ := hstr _ hy
  obtain ⟨ψ, hψ⟩ := exists_pullback_iso_sigma (f ≫ (complementOpen D).ι).fromNormalization
    V.2 hpre A (fun i ↦ standardRing A ((u i : A) * algebraMap Γ(X, V) A a) (e i)) g
  obtain ⟨hφ, hxφ⟩ := chart_etale_mem_range V.2 hxV A hy'
  obtain ⟨χ, hχ⟩ := exists_pullback_subschemeι_iso D hDa A
  exact ⟨CommRingCat.of A, _, hφ, hxφ, hAN, algebraMap Γ(X, V) A a, haA, hregA, ⟨χ, hχ⟩,
    n, e, u, fun i ↦ ⟨he i, heu i⟩, ψ, hψ⟩

/-- The chart at a point outside `D`: `a = 1`, `u_i = 1`, `e_i = 1`. -/
theorem isAbhyankarChartAt_of_notMem [IsLocallyNoetherian X]
    {D : X.IdealSheafData} (hD : IsEffectiveCartier D)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f] (x : X)
    (hxD : x ∉ D.support) :
    IsAbhyankarChartAt D (f ≫ (complementOpen D).ι).fromNormalization x := by
  obtain ⟨V₀, hxV₀, a₀, -, hDa₀⟩ := hD x
  let V : X.affineOpens := X.affineBasicOpen a₀
  have hxV : x ∈ V.1 := by
    have := (mem_support_iff_of_ideal_eq hDa₀ hxV₀).not.mp hxD
    rwa [not_not] at this
  have hVU : V.1 ≤ complementOpen D := by
    change X.basicOpen a₀ ≤ _
    rw [← inf_eq_basicOpen_of_ideal_eq hDa₀]; exact inf_le_left
  have hDV : D.ideal V = Ideal.span {1} := by
    rw [Ideal.span_singleton_one, ← D.map_ideal_basicOpen, hDa₀, Ideal.map_span,
      Set.image_singleton]
    exact Ideal.span_singleton_eq_top.mpr (X.toRingedSpace.isUnit_res_basicOpen a₀)
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
  have h1 : ((1 : Aˣ) : A) * algebraMap Γ(X, V) A 1 = 1 := by simp
  let g' : A ⊗[Γ(X, V)] Γ((f ≫ (complementOpen D).ι).normalization,
      (f ≫ (complementOpen D).ι).fromNormalization ⁻¹ᵁ V.1) ≃ₐ[A]
        ∀ _i : Fin n, standardRing A (((1 : Aˣ) : A) * algebraMap Γ(X, V) A 1) 1 := by
    rw [h1]
    exact (F'.trans g).trans (AlgEquiv.piCongrRight fun _ ↦
      (standardRingOneOneEquiv (A := A)).symm)
  obtain ⟨ψ, hψ⟩ := exists_pullback_iso_sigma (f ≫ (complementOpen D).ι).fromNormalization
    V.2 hpre A (fun _ ↦ standardRing A (((1 : Aˣ) : A) * algebraMap Γ(X, V) A 1) 1) g'
  obtain ⟨hφ, hxφ⟩ := chart_etale_mem_range V.2 hxV A hy'
  obtain ⟨χ, hχ⟩ := exists_pullback_subschemeι_iso D hDV A
  have hone : algebraMap Γ(X, V) A 1 = 1 := map_one _
  refine ⟨CommRingCat.of A, _, hφ, hxφ, hAN, algebraMap Γ(X, V) A 1, ?_, ?_, ⟨χ, hχ⟩,
    n, fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ ⟨le_rfl, by simp⟩, ψ, hψ⟩
  · rw [hone]; exact one_mem _
  · have : Subsingleton (A ⧸ Ideal.span {algebraMap Γ(X, V) A 1}) := by
      rw [hone, Ideal.span_singleton_one]; infer_instance
    exact isRegularRing_of_subsingleton _

/-- **`paper.tex`, Theorem `thm:abhyankar` (Abhyankar's lemma), in the explicit form
of the manuscript.** Let `U = X` be locally Noetherian, `D` an effective Cartier
divisor which is a regular scheme, and `W → U ∖ D` finite étale and tamely
ramified over `U` in codimension one; let `π : V → U` be the normalization of `U`
in `W`. Then every point of `U` lies in the image of an étale `φ : Spec R → U`
with `R` Noetherian and a nonzerodivisor `a ∈ R` with `R/aR` regular, such that
`D ×_U Spec R ≅ Spec (R/aR)` over `Spec R` (equivalently `φ*D = V(a)` as ideal
sheaves), and `V ×_U Spec R ≅ ∐_i Spec R[z]/(z^{e_i} - u_i a)` over `Spec R` for
finitely many units `u_i` and integers `e_i ≥ 1` invertible in `R`.

Manuscript: `thm:abhyankar` (Theorem 6.2). -/
theorem abhyankar_lemma (X : Scheme.{u}) [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsEffectiveCartier D) (hDreg : IsRegularScheme D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (complementOpen D) f) :
    ∀ x : X, ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ X), Etale φ ∧ x ∈ Set.range φ ∧
      IsNoetherianRing R ∧
      ∃ a : R, a ∈ nonZeroDivisors R ∧ IsRegularRing (R ⧸ Ideal.span {a}) ∧
        (∃ χ : pullback φ D.subschemeι ≅ Spec (CommRingCat.of (R ⧸ Ideal.span {a})),
          χ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = pullback.fst _ _) ∧
        D.comap φ = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))).ker ∧
        ∃ (n : ℕ) (e : Fin n → ℕ) (u : Fin n → Rˣ), (∀ i, 1 ≤ e i ∧ IsUnit (e i : R)) ∧
          ∃ ψ : pullback (f ≫ (complementOpen D).ι).fromNormalization φ ≅
              ∐ (fun i ↦ Spec (CommRingCat.of (standardRing R ((u i : R) * a) (e i)))),
            ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
              (algebraMap R (standardRing R ((u i : R) * a) (e i))))) =
              pullback.snd (f ≫ (complementOpen D).ι).fromNormalization φ := by
  intro x
  have hA := abhyankarLemmaTameOver_of_forall X Pcf.Stacks.abhyankarLemmaTameOfFinite
  have hchart : IsAbhyankarChartAt D (f ≫ (complementOpen D).ι).fromNormalization x := by
    by_cases hxD : x ∈ D.support
    · exact isAbhyankarChartAt_of_mem hA hD hDreg f htame x hxD
    · exact isAbhyankarChartAt_of_notMem hD f x hxD
  obtain ⟨R, φ, hφ, hxφ, hRN, a, ha, hreg, ⟨χ, hχ⟩, rest⟩ := hchart
  refine ⟨R, φ, hφ, hxφ, hRN, a, ha, hreg, ⟨χ, hχ⟩, ?_, rest⟩
  rw [Scheme.IdealSheafData.comap, ← hχ, Scheme.Hom.ker_comp_of_isIso]

#print axioms subschemeAppAlgEquiv
#print axioms exists_pullback_subschemeι_iso
#print axioms chart_etale_mem_range
#print axioms IsAbhyankarChartAt
#print axioms isAbhyankarChartAt_of_mem
#print axioms isAbhyankarChartAt_of_notMem
#print axioms abhyankar_lemma

end Pcf.PaperCharZero
