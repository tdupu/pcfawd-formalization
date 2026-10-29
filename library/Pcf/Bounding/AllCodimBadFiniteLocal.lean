/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBadFiniteTopology
public import Pcf.Bounding.ClosureStalk
public import Pcf.Bounding.NonNormalCodimOne
public import Pcf.Bounding.InvariantDivisorGeometry
public import Pcf.Bounding.FiniteSingularCorrection
public import Pcf.Stacks.Purity.DimensionOne
public import Pcf.Stacks.Common.AffineBasicOpen

/-!
# Local finiteness of bad points on an exceptional divisor

Fix a codimension-one point `d` of a Noetherian integral scheme `Y`. Among the
codimension-two points `E` on the closure of `d`, only finitely many have a
reduced closure stalk that is not a discrete valuation ring, and outside a
closed set avoiding `d` the prime of `d` at `E` is principal. These are two of
the conditions defining the finite bad set in `latex/paper-p.tex`, proof of
Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {Y : Scheme.{u}}

/-- A point of the reduced closure of a codimension-one point `d` whose image
has codimension two has codimension one in the closure. -/
theorem coheight_pointClosure_eq_one [IsIntegral Y] (d : Y) (hd : Order.coheight d = 1)
    (e : (pointClosureIdealSheaf d).subscheme)
    (he : Order.coheight ((pointClosureIdealSheaf d).subschemeι e) = 2) :
    Order.coheight e = 1 := by
  let ι := (pointClosureIdealSheaf d).subschemeι
  let ξ := genericPoint (pointClosureIdealSheaf d).subscheme
  have hξ : ι ξ = d := pointClosureSubscheme_genericPoint d
  have hemb := ι.isEmbedding.isInducing
  -- strict monotonicity of `ι` for the specialization order
  have hmono : ∀ {a b}, a < b → ι a < ι b := by
    intro a b hab
    refine lt_of_le_not_ge (hab.le.map ι.continuous) fun h => hab.not_ge ?_
    exact hemb.specializes_iff.mp h
  have hξe : ξ ⤳ e := (genericPoint_spec _).specializes trivial
  have hne : e ≠ ξ := by
    intro h
    rw [h, hξ, hd] at he
    exact absurd he (by norm_num)
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h2 : ((2 : ℕ) : ℕ∞) ≤ Order.coheight e := by
      have : (1 : ℕ∞) < Order.coheight e := hlt
      exact Order.add_one_le_of_lt this
    obtain ⟨c, hc0, hc2⟩ := Order.exists_series_of_le_coheight e h2
    let i0 : Fin c.length := ⟨0, by omega⟩
    let i1 : Fin c.length := ⟨1, by omega⟩
    have h01 : c.toFun i0.castSucc < c.toFun i0.succ := c.step i0
    have h12 : c.toFun i1.castSucc < c.toFun i1.succ := c.step i1
    have hc0' : c.toFun i0.castSucc = e := hc0
    have hmid : c.toFun i0.succ = c.toFun i1.castSucc := rfl
    rw [hc0'] at h01
    rw [hmid] at h01
    set a := c.toFun i1.castSucc
    set b := c.toFun i1.succ
    have hb : ι b ≤ d := by
      have := ((genericPoint_spec (pointClosureIdealSheaf d).subscheme).specializes
        (Set.mem_univ b)).map ι.continuous
      rw [hξ] at this
      exact this
    have hdη : d < genericPoint Y := by
      have hle : genericPoint Y ⤳ d := (genericPoint_spec Y).specializes trivial
      refine lt_of_le_not_ge hle fun h => ?_
      have heq : d = genericPoint Y := (Specializes.antisymm h hle).eq
      rw [heq] at hd
      have h0 : Order.coheight (genericPoint Y) = 0 := by
        rw [Order.coheight_eq_zero]
        intro z hz
        exact (genericPoint_spec Y).specializes (Set.mem_univ z)
      rw [h0] at hd
      exact absurd hd (by norm_num)
    have hbη : ι b < genericPoint Y := lt_of_le_of_lt hb hdη
    have c1 := Order.coheight_add_one_le (hmono h01)
    have c2 := Order.coheight_add_one_le (hmono h12)
    have c3 := Order.coheight_add_one_le hbη
    rw [he] at c1
    have : (2 : ℕ∞) ≥ 0 + 1 + 1 + 1 := by
      calc (2 : ℕ∞) ≥ Order.coheight (ι a) + 1 := c1
        _ ≥ Order.coheight (ι b) + 1 + 1 := by gcongr
        _ ≥ Order.coheight (genericPoint Y) + 1 + 1 + 1 := by gcongr
        _ ≥ 0 + 1 + 1 + 1 := by gcongr; exact zero_le
    exact absurd this (by norm_num)
  · have hlt : e < ξ := lt_of_le_not_ge hξe fun h => hne (Specializes.antisymm hξe h).eq.symm
    have := Order.coheight_add_one_le hlt
    simpa using (le_add_self).trans this

/-- A point specialized from `d` lies in the image of the reduced closure. -/
theorem mem_range_pointClosure_of_specializes {d E : Y} (h : d ⤳ E) :
    E ∈ Set.range (pointClosureIdealSheaf d).subschemeι := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  unfold pointClosureIdealSheaf
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact specializes_iff_mem_closure.mp h

/-- **Finiteness of non-regular divisor points.** On the closure of a
codimension-one point `d`, the codimension-two points at which the reduced
closure is not a discrete valuation ring are finitely many. -/
theorem finite_closureStalk_not_dvr [IsIntegral Y] [IsLocallyNoetherian Y] [NoetherianSpace Y]
    (k : Type u) [Field k] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (d : Y) (hd : Order.coheight d = 1) :
    {E : Y | ∃ h : d ⤳ E, Order.coheight E = 2 ∧
      ¬ IsDiscreteValuationRing (closureStalk Y h)}.Finite := by
  let ιD := (pointClosureIdealSheaf d).subschemeι
  let D := (pointClosureIdealSheaf d).subscheme
  haveI : LocallyOfFiniteType (ιD ≫ sY) := inferInstance
  have hN := finite_nonNormal_schemeDivisorPoint k (ιD ≫ sY)
  refine (hN.image fun Q => ιD Q.1).subset ?_
  rintro E ⟨h, hE2, hbad⟩
  obtain ⟨e, rfl⟩ := mem_range_pointClosure_of_specializes h
  have he1 : Order.coheight e = 1 := coheight_pointClosure_eq_one d hd e hE2
  refine ⟨⟨e, he1⟩, ?_, rfl⟩
  intro hic
  apply hbad
  let eqv := pointClosureStalkEquiv d e h
  letI : IsIntegrallyClosed (closureStalk Y h) := IsIntegrallyClosed.of_equiv eqv.symm
  have hdim : ringKrullDim (closureStalk Y h) = 1 := by
    rw [eqv.ringKrullDim, AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, he1]
    rfl
  exact Pcf.Stacks.isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one _ hdim

/-- On an affine open, the prime of a generization `d ⤳ E` in the stalk at `E`
is the extension of the affine prime of `d`. -/
theorem stalkGenerizationPrime_eq_map {d E : Y} (h : d ⤳ E) (W : Y.affineOpens)
    (hE : E ∈ (W : Y.Opens)) :
    stalkGenerizationPrime Y h =
      (W.2.primeIdealOf ⟨d, h.mem_open W.1.isOpen hE⟩).asIdeal.map
        (Y.presheaf.germ W E hE).hom := by
  have hdW : d ∈ (W : Y.Opens) := h.mem_open W.1.isOpen hE
  let R := Γ(Y, W)
  let 𝔭 : Ideal R := (W.2.primeIdealOf ⟨d, hdW⟩).asIdeal
  let q : Ideal R := (W.2.primeIdealOf ⟨E, hE⟩).asIdeal
  letI : Algebra R (Y.presheaf.stalk E) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨E, hE⟩
  letI : Algebra R (Y.presheaf.stalk d) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨d, hdW⟩
  haveI hlocE : IsLocalization.AtPrime (Y.presheaf.stalk E) q :=
    W.2.isLocalization_stalk ⟨E, hE⟩
  haveI hlocd : IsLocalization.AtPrime (Y.presheaf.stalk d) 𝔭 :=
    W.2.isLocalization_stalk ⟨d, hdW⟩
  have hspec (r : R) : (Y.presheaf.stalkSpecializes h).hom (algebraMap R _ r) =
      algebraMap R (Y.presheaf.stalk d) r := by
    change (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ W E hE).hom r) =
      (Y.presheaf.germ W d hdW).hom r
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  apply le_antisymm
  · intro s hs
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl s
    dsimp only at hs ⊢
    have hs' : (Y.presheaf.stalkSpecializes h).hom (IsLocalization.mk' _ r t) ∈
        maximalIdeal (Y.presheaf.stalk d) := hs
    have hunit : IsUnit ((Y.presheaf.stalkSpecializes h).hom (algebraMap R _ (t : R))) :=
      (IsLocalization.map_units (Y.presheaf.stalk E) t).map _
    have hr : algebraMap R (Y.presheaf.stalk d) r ∈ maximalIdeal (Y.presheaf.stalk d) := by
      rw [← hspec, ← IsLocalization.mk'_spec (Y.presheaf.stalk E) r t, map_mul]
      exact Ideal.mul_mem_right _ _ hs'
    have hr𝔭 : r ∈ 𝔭 := (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔭 r).mp hr
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem (algebraMap R _) hr𝔭)
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ W E hE).hom r) ∈
      maximalIdeal (Y.presheaf.stalk d)
    have := hspec r
    change (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ W E hE).hom r) =
      algebraMap R (Y.presheaf.stalk d) r at this
    rw [this]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔭 r).mpr hr

/-- **Principal generation off a closed set.** For a codimension-one point `d`
of a normal locally Noetherian integral scheme, there is a closed set avoiding
`d` outside of which the prime of `d` is principal in every stalk below `d`. -/
theorem exists_isClosed_stalkGenerizationPrime_isPrincipal [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] (d : SchemeDivisorPoint Y) :
    ∃ Z : Set Y, IsClosed Z ∧ d.1 ∉ Z ∧
      ∀ (E : Y) (h : d.1 ⤳ E), E ∉ Z → (stalkGenerizationPrime Y h).IsPrincipal := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hdV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ d.1) isOpen_univ
  let W : Y.affineOpens := ⟨V, hV⟩
  let R := Γ(Y, W)
  let 𝔭 : Ideal R := (W.2.primeIdealOf ⟨d.1, hdV⟩).asIdeal
  haveI : Nonempty (W : Y.Opens) := ⟨⟨d.1, hdV⟩⟩
  haveI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian W
  haveI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed W
  have h𝔭 : 𝔭.height = 1 := by
    have := pointClosureIdealSheaf_ideal_height d W hdV
    rwa [pointClosureIdealSheaf_ideal d.1 W hdV] at this
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne 𝔭 h𝔭
  haveI : (𝔭.map (algebraMap R (Localization.AtPrime 𝔭))).IsPrincipal :=
    IsPrincipalIdealRing.principal _
  obtain ⟨a, -, f, hf𝔭, hf⟩ :=
    exists_principalOpen_map_eq_span_of_isPrincipal_atPrime 𝔭 (Ideal.fg_of_isNoetherianRing 𝔭) 𝔭
  let S : Set Y := (W : Set Y) \ (Y.basicOpen f : Set Y)
  have hdf : d.1 ∈ Y.basicOpen f :=
    (Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf W.2 f ⟨d.1, hdV⟩).mpr hf𝔭
  refine ⟨(W : Set Y)ᶜ ∪ closure S, W.1.isOpen.isClosed_compl.union isClosed_closure, ?_, ?_⟩
  · rintro (h | h)
    · exact h hdV
    · have hopen : IsOpen ((W : Set Y) ∩ Y.basicOpen f) := W.1.isOpen.inter (Y.basicOpen f).isOpen
      obtain ⟨z, ⟨hzW, hzf⟩, hzS⟩ :=
        mem_closure_iff.mp h _ hopen ⟨hdV, hdf⟩
      exact hzS.2 hzf
  · intro E h hE
    have hEW : E ∈ (W : Y.Opens) := by
      by_contra hn
      exact hE (Or.inl hn)
    have hEf : E ∈ Y.basicOpen f := by
      by_contra hn
      exact hE (Or.inr (subset_closure ⟨hEW, hn⟩))
    let q : Ideal R := (W.2.primeIdealOf ⟨E, hEW⟩).asIdeal
    have hfq : f ∉ q :=
      (Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf W.2 f ⟨E, hEW⟩).mp hEf
    rw [stalkGenerizationPrime_eq_map h W hEW]
    letI : Algebra R (Y.presheaf.stalk E) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨E, hEW⟩
    haveI : IsLocalization.AtPrime (Y.presheaf.stalk E) q := W.2.isLocalization_stalk ⟨E, hEW⟩
    let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (Y.presheaf.stalk E)
    have hgerm : (Y.presheaf.germ W E hEW).hom = (e : Localization.AtPrime q →+* _).comp
        (algebraMap R (Localization.AtPrime q)) := by
      ext r
      exact (e.commutes r).symm
    refine ⟨⟨e (algebraMap R (Localization.AtPrime q) a), ?_⟩⟩
    change 𝔭.map (Y.presheaf.germ W E hEW).hom = _
    rw [hgerm, ← Ideal.map_map, hf q hfq, Ideal.map_span, Set.image_singleton]
    rfl

/-- A codimension-one point is not in the closure of a different
codimension-one point. -/
theorem not_mem_closure_of_coheight_one {d w : Y} (hd : Order.coheight d = 1)
    (hw : Order.coheight w = 1) (hne : w ≠ d) : d ∉ closure ({w} : Set Y) := by
  intro hmem
  have hwd : w ⤳ d := specializes_iff_mem_closure.mpr hmem
  have hlt : d < w := lt_of_le_not_ge hwd fun h => hne (Specializes.antisymm hwd h).eq
  have := Order.coheight_add_one_le hlt
  rw [hd, hw] at this
  exact absurd this (by norm_num)

/-- **Finiteness of the non-primary bad points on one exceptional divisor.**
For a codimension-one point `d`, the codimension-two points `E` below `d` at
which the prime of `d` is not principal, the reduced closure is not a discrete
valuation ring, or another divisor of the finite set `W` passes through `E`,
are finitely many. -/
theorem finite_bad_exceptional_points [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormalScheme Y] [NoetherianSpace Y]
    (k : Type u) [Field k] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    {X : Scheme.{u}} (β : Y ⟶ X) (y : X) (B : Set X) (d : SchemeDivisorPoint Y)
    (hW : {w : Y | Order.coheight w = 1 ∧ (y ⤳ β w ∨ β w ∈ B)}.Finite) :
    {E : Y | ∃ h : d.1 ⤳ E, Order.coheight E = 2 ∧
      ¬ ((stalkGenerizationPrime Y h).IsPrincipal ∧
        IsDiscreteValuationRing (closureStalk Y h) ∧
        ∀ w : SchemeDivisorPoint Y, w.1 ⤳ E → w ≠ d → ¬ y ⤳ β w.1 ∧ β w.1 ∉ B)}.Finite := by
  obtain ⟨Z, hZ, hdZ, hprin⟩ := exists_isClosed_stalkGenerizationPrime_isPrincipal d
  have F1 := finite_coheight_two_of_isClosed d.1 d.2 Z hZ hdZ
  have F2 := finite_closureStalk_not_dvr k sY d.1 d.2
  have F3 : (⋃ w ∈ {w : Y | (Order.coheight w = 1 ∧ (y ⤳ β w ∨ β w ∈ B)) ∧ w ≠ d.1},
      {E : Y | E ∈ closure ({w} : Set Y) ∧ d.1 ⤳ E ∧ Order.coheight E = 2}).Finite := by
    refine Set.Finite.biUnion (hW.subset fun w hw => hw.1) fun w hw => ?_
    exact finite_coheight_two_of_isClosed d.1 d.2 _ isClosed_closure
      (not_mem_closure_of_coheight_one d.2 hw.1.1 hw.2)
  refine ((F1.union F2).union F3).subset ?_
  rintro E ⟨h, hE2, hbad⟩
  by_cases hEZ : E ∈ Z
  · exact Or.inl (Or.inl ⟨hEZ, h, hE2⟩)
  by_cases hdvr : IsDiscreteValuationRing (closureStalk Y h)
  · have hiso : ¬ ∀ w : SchemeDivisorPoint Y, w.1 ⤳ E → w ≠ d →
        ¬ y ⤳ β w.1 ∧ β w.1 ∉ B := fun hall => hbad ⟨hprin E h hEZ, hdvr, hall⟩
    push Not at hiso
    obtain ⟨w, hwE, hwd, hw⟩ := hiso
    refine Or.inr (Set.mem_biUnion (x := w.1) ⟨⟨w.2, ?_⟩, ?_⟩
      ⟨specializes_iff_mem_closure.mp hwE, h, hE2⟩)
    · by_cases hy : y ⤳ β w.1
      · exact Or.inl hy
      · exact Or.inr (hw hy)
    · exact fun heq => hwd (Subtype.ext heq)
  · exact Or.inl (Or.inr ⟨h, hE2, hdvr⟩)

end
end Pcf
