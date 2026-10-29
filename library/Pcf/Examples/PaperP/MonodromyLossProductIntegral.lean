/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossProduct
public import Pcf.Examples.PaperP.MonodromyLossYFinite
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# `E ×ₖ ℙ¹` is integral (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: the source of `F(P, z) = (φ(P), 1/z)` is
`E × ℙ¹`. Here `EP1 = E ×ₖ ℙ¹` is shown to be an integral scheme.

* `A1toSpec`: `𝔸¹ = Spec k[X] → Spec k`; it is geometrically integral, flat and universally
  open (transported from Mathlib's `𝔸(n; S)`).
* `chartP1 e`: the two standard affine charts `𝔸¹ → ℙ¹` (`e = refl` is `D₊(v)`,
  `e = swap` is `D₊(u)`), and `chartEP1 e : E ×ₖ 𝔸¹ ⟶ E ×ₖ ℙ¹` their base changes; the
  sources `E ×ₖ 𝔸¹` are integral by Mathlib (`E` integral and locally noetherian).
* **`EP1_isIntegral`**: the two charts cover `EP1`, and they meet (over a point of `ℙ¹` in
  `D₊(u) ∩ D₊(v)`, e.g. `y(P)` for `P ∈ U_A ∩ U_B`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial

namespace Pcf.Examples.PaperP.MonodromyLossProductIntegral

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k]

/-- The polynomial ring `k[X]` of the affine line. -/
abbrev Poly := MvPolynomial (Fin 1) k

/-- `𝔸¹ = Spec k[X] → Spec k`. -/
noncomputable abbrev A1toSpec : Spec (.of (Poly k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Poly k)))

/-- Renaming `Fin 1 ≃ ULift (Fin 1)`. -/
noncomputable def renameU : MvPolynomial (ULift.{u} (Fin 1)) k ≃ₐ[k] Poly k :=
  renameEquiv k Equiv.ulift

instance renameU_isIso :
    IsIso (CommRingCat.ofHom (renameU k).toRingEquiv.toRingHom) :=
  inferInstanceAs (IsIso (renameU k).toRingEquiv.toCommRingCatIso.hom)

theorem A1toSpec_eq : A1toSpec k =
    Spec.map (CommRingCat.ofHom (renameU k).toRingEquiv.toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).inv ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) := by
  rw [AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  simp [renameU, MvPolynomial.algebraMap_eq]

instance A1toSpec_geometricallyIntegral : GeometricallyIntegral (A1toSpec k) := by
  rw [A1toSpec_eq, ← Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
  infer_instance

instance A1toSpec_flat : Flat (A1toSpec k) := by
  rw [A1toSpec_eq, ← Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
  infer_instance

instance A1toSpec_universallyOpen : UniversallyOpen (A1toSpec k) := by
  rw [A1toSpec_eq, ← Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @UniversallyOpen)]
  infer_instance

instance E_isLocallyNoetherian : IsLocallyNoetherian (E k) :=
  LocallyOfFiniteType.isLocallyNoetherian (toSpec k)

/-- `E ×ₖ 𝔸¹`. -/
noncomputable abbrev EA1 : Scheme.{u} := pullback (toSpec k) (A1toSpec k)

instance EA1_isIntegral : IsIntegral (EA1 k) := inferInstance

/-- The standard chart `𝔸¹ → ℙ¹` onto `D₊(X (e⁻¹ ∞))`. -/
noncomputable abbrev chartP1 (e : Index ≃ Index) :
    Spec (.of (Poly k)) ⟶ Proj (grading k) :=
  Pcf.paperPAnyTargetChartToProj (K := k) (n := 1) e

theorem chartP1_structureMap (e : Index ≃ Index) :
    chartP1 k e ≫ BasilicaProjectiveScheme.structureMap k = A1toSpec k :=
  BasilicaProjectiveScheme.anyTargetChart_comp_structureMap k e

/-- The chart `E ×ₖ 𝔸¹ ⟶ E ×ₖ ℙ¹`. -/
noncomputable def chartEP1 (e : Index ≃ Index) : EA1 k ⟶ EP1 k :=
  pullback.map (toSpec k) (A1toSpec k) (toSpec k) (BasilicaProjectiveScheme.structureMap k)
    (𝟙 _) (chartP1 k e) (𝟙 _) (by simp) (by rw [Category.comp_id, chartP1_structureMap])

instance chartEP1_isOpenImmersion (e : Index ≃ Index) : IsOpenImmersion (chartEP1 k e) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstance : IsOpenImmersion (𝟙 _))
    (inferInstance : IsOpenImmersion (chartP1 k e)) (Category.id_comp _).symm
    (chartP1_structureMap k e).symm

theorem range_chartEP1 (e : Index ≃ Index) :
    Set.range (chartEP1 k e) = pullback.snd (toSpec k) (BasilicaProjectiveScheme.structureMap k)
      ⁻¹' Set.range (chartP1 k e) := by
  rw [chartEP1, Scheme.Pullback.range_map]
  simp

theorem range_chartP1 (e : Index ≃ Index) (j : Index) (hj : e.symm (Sum.inr ()) = j) :
    Set.range (chartP1 k e) = Set.range (Proj.awayι (grading k) (X j)
      (isHomogeneous_X k _) Nat.zero_lt_one) := by
  subst hj
  let r := Pcf.paperPAnyTargetChartRingEquiv (K := k) (n := 1) e
  have : IsIso (CommRingCat.ofHom r.toRingHom) :=
    inferInstanceAs (IsIso r.toCommRingCatIso.hom)
  rw [chartP1, Pcf.paperPAnyTargetChartToProj, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  exact (ConcreteCategory.bijective_of_isIso (Spec.map (CommRingCat.ofHom r.toRingHom)).base).2

/-- `e` with `e⁻¹ ∞ = u`. -/
abbrev eU : Index ≃ Index := Equiv.swap (Sum.inl 0) (Sum.inr ())

theorem chartP1_cover (p : Proj (grading k)) :
    p ∈ Set.range (chartP1 k (Equiv.refl _)) ∨ p ∈ Set.range (chartP1 k (eU)) := by
  rw [range_chartP1 k _ (Sum.inr ()) rfl, range_chartP1 k _ (Sum.inl 0) (by decide)]
  have hi := (P1Cover k).covers p
  generalize (P1Cover k).idx p = i at hi
  rcases i with i | i
  · have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    right
    exact hi
  · left
    exact hi

theorem toSpec_surjective : Surjective (toSpec k) := by
  constructor
  intro s
  exact ⟨genericPoint (E k), Subsingleton.elim _ _⟩

instance snd_surjective : Surjective (pullback.snd (toSpec k)
    (BasilicaProjectiveScheme.structureMap k)) :=
  haveI := toSpec_surjective k
  MorphismProperty.pullback_snd _ _ inferInstance

theorem exists_point_both_charts : ∃ p : Proj (grading k),
    p ∈ Set.range (chartP1 k (Equiv.refl _)) ∧ p ∈ Set.range (chartP1 k (eU)) := by
  obtain ⟨x, hA, hB⟩ := range_ιA_inter_range_ιB_nonempty k
  refine ⟨yMap k x, ?_, ?_⟩
  · rw [range_chartP1 k _ (Sum.inr ()) rfl]
    have : x ∈ (ιA k).opensRange := hA
    rw [← yMap_preimage_v] at this
    exact this
  · rw [range_chartP1 k _ (Sum.inl 0) (by decide)]
    have : x ∈ (ιB k).opensRange := hB
    rw [← yMap_preimage_u] at this
    exact this

instance EP1_irreducibleSpace : IrreducibleSpace (EP1 k) := by
  have hU : IsIrreducible (Set.range (chartEP1 k (Equiv.refl _))) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (chartEP1 k _).continuous.continuousOn
  have hV : IsIrreducible (Set.range (chartEP1 k eU)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (chartEP1 k _).continuous.continuousOn
  have hne : (Set.range (chartEP1 k eU) ∩ Set.range (chartEP1 k (Equiv.refl _))).Nonempty := by
    obtain ⟨p, h1, h2⟩ := exists_point_both_charts k
    obtain ⟨z, hz⟩ := (snd_surjective k).surj p
    refine ⟨z, ?_, ?_⟩
    · rw [range_chartEP1, Set.mem_preimage, hz]; exact h2
    · rw [range_chartEP1, Set.mem_preimage, hz]; exact h1
  have hcl : closure (Set.range (chartEP1 k (Equiv.refl _))) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    rcases chartP1_cover k
        (pullback.snd (toSpec k) (BasilicaProjectiveScheme.structureMap k) z) with h | h
    · exact subset_closure (by rw [range_chartEP1]; exact h)
    · have hz : z ∈ Set.range (chartEP1 k eU) := by rw [range_chartEP1]; exact h
      have := subset_closure_inter_of_isPreirreducible_of_isOpen hV.2
        (chartEP1 k (Equiv.refl _)).isOpenEmbedding.isOpen_range hne hz
      exact closure_mono Set.inter_subset_right this
  rw [irreducibleSpace_def]
  simpa [hcl] using hU.closure

instance EP1_isReduced : IsReduced (EP1 k) := by
  have : ∀ z : EP1 k, _root_.IsReduced ((EP1 k).presheaf.stalk z) := by
    intro z
    have key : ∀ e : Index ≃ Index, z ∈ Set.range (chartEP1 k e) →
        _root_.IsReduced ((EP1 k).presheaf.stalk z) := by
      rintro e ⟨w, rfl⟩
      exact isReduced_of_injective _
        (ConcreteCategory.bijective_of_isIso ((chartEP1 k e).stalkMap w)).1
    rcases chartP1_cover k
        (pullback.snd (toSpec k) (BasilicaProjectiveScheme.structureMap k) z) with h | h
    · exact key _ (by rw [range_chartEP1]; exact h)
    · exact key _ (by rw [range_chartEP1]; exact h)
  exact isReduced_of_isReduced_stalk _

/-- **`E ×ₖ ℙ¹` is integral.** -/
instance EP1_isIntegral : IsIntegral (EP1 k) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

#print axioms EP1_isIntegral

end Pcf.Examples.PaperP.MonodromyLossProductIntegral
