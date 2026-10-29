/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBadFinitePrimary
public import Pcf.Bounding.PrimaryFibresCharZeroScheme

/-!
# The fibre-multiplicity condition in characteristic zero

The characteristic-zero form of `exists_finite_primary_bad`: off a finite set,
the fibre multiplicity `μ(E/x)` of the closure of a codimension-one point over
the closure of the centre is one. It applies the characteristic-zero form of
`lem:primary-fibres` of `latex/paper-p.tex`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- **Fibre multiplicity one off a finite set** (characteristic zero). -/
theorem exists_finite_primary_bad_charZero (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [IsIntegral Y] [NoetherianSpace Y] (β : Y ⟶ X) [LocallyOfFiniteType (β ≫ s)]
    (y : X) (d : SchemeDivisorPoint Y) (hβd : β d.1 = y) :
    ∃ S : Set X, S.Finite ∧ ∀ (E : Y) (h : d.1 ⤳ E), Order.coheight E = 2 →
      IsDiscreteValuationRing (closureStalk Y h) →
      (∃ Q : SchemeDivisorPoint (pointClosureIdealSheaf y).subscheme,
        (pointClosureIdealSheaf y).subschemeι Q.1 = β E) →
      IsDiscreteValuationRing (closureStalk X (h.map β.continuous)) →
      β E ∉ S → closureFibreMultiplicity β h = 1 := by
  subst hβd
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (β ≫ s)
  let A := (pointClosureIdealSheaf (β d.1)).subscheme
  let ιA : A ⟶ X := (pointClosureIdealSheaf (β d.1)).subschemeι
  let D := (pointClosureIdealSheaf d.1).subscheme
  let ιD : D ⟶ Y := (pointClosureIdealSheaf d.1).subschemeι
  let qD : D ⟶ A := pointClosureSubschemeMap β d.1 (β d.1) rfl
  haveI : IsDominant qD := pointClosureSubschemeMap_isDominant β d.1 (β d.1) rfl
  have hqD : qD ≫ ιA = ιD ≫ β := pointClosureSubschemeMap_subschemeι β d.1 (β d.1) rfl
  let sA : A ⟶ Spec (.of k) := ιA ≫ s
  let sD : D ⟶ Spec (.of k) := ιD ≫ (β ≫ s)
  letI : IsFinite (Palomar.normalizationMap A) := schemeGlobalNormalizationMap_isFinite A k sA
  letI : IsFinite (Palomar.normalizationMap D) := schemeGlobalNormalizationMap_isFinite D k sD
  let Aν := Palomar.normalization A
  let Dν := Palomar.normalization D
  let νA : Aν ⟶ A := Palomar.normalizationMap A
  let νD : Dν ⟶ D := Palomar.normalizationMap D
  let ψ : Dν ⟶ A := νD ≫ qD
  haveI : IsDominant ψ := inferInstance
  let qν : Dν ⟶ Aν := normalDominantNormalizationLift ψ
  have hqν : qν ≫ νA = ψ := normalDominantNormalizationLift_comp ψ
  let sAν : Aν ⟶ Spec (.of k) := νA ≫ sA
  haveI : LocallyOfFiniteType (qν ≫ sAν) := by
    have : qν ≫ sAν = νD ≫ ιD ≫ (β ≫ s) := by
      simp only [sAν, sA, ← Category.assoc, hqν]
      simp only [ψ, Category.assoc, ← reassoc_of% hqD]
    rw [this]
    infer_instance
  haveI : LocallyOfFiniteType qν := locallyOfFiniteType_of_comp qν sAν
  haveI : IsLocallyNoetherian Aν := LocallyOfFiniteType.isLocallyNoetherian sAν
  haveI : LocallyOfFiniteType (νD ≫ sD) := inferInstance
  haveI : IsLocallyNoetherian Dν := LocallyOfFiniteType.isLocallyNoetherian (νD ≫ sD)
  haveI : CompactSpace Aν := QuasiCompact.compactSpace_of_compactSpace νA
  haveI : CompactSpace Dν := QuasiCompact.compactSpace_of_compactSpace νD
  haveI : QuasiCompact qν := by
    haveI : QuasiCompact (qν ≫ sAν) := inferInstance
    exact QuasiCompact.of_comp qν sAν
  obtain ⟨Uo, hUo, hfib⟩ :=
    Bounding.exists_open_schemeDivisorRamificationIdx_eq_one_charZero k sAν qν
  -- the finite bad set
  let C : Set A := νA '' ((Uo : Set Aν)ᶜ)
  have hCcl : IsClosed C := νA.isClosedMap _ Uo.isOpen.isClosed_compl
  have hgenU : genericPoint Aν ∈ Uo := by
    obtain ⟨w, hw⟩ := hUo
    exact ((genericPoint_spec Aν).mem_open_set_iff Uo.isOpen).mpr ⟨w, trivial, hw⟩
  have hgenC : genericPoint A ∉ C := by
    rintro ⟨z, hzU, hz⟩
    have hη : νA (genericPoint Aν) = genericPoint A := map_genericPoint_eq_of_isDominant νA
    haveI : IsIntegrallyClosed (A.presheaf.stalk (νA z)) := by
      rw [hz]
      change IsIntegrallyClosed A.functionField
      infer_instance
    have hzη : z = genericPoint Aν :=
      normalizationMap_eq_of_apply_eq_of_isIntegrallyClosed A z _ (hz.trans hη.symm)
    exact hzU (hzη ▸ hgenU)
  have hS0 := finite_coheight_one_of_isClosed C hCcl hgenC
  refine ⟨ιA '' {x : A | x ∈ C ∧ Order.coheight x = 1}, hS0.image _, ?_⟩
  intro E h hE2 hDdvr ⟨Q, hQ⟩ hXdvr hES
  obtain ⟨e, rfl⟩ := mem_range_pointClosure_of_specializes h
  have he1 : Order.coheight e = 1 := coheight_pointClosure_eq_one d.1 d.2 e hE2
  haveI : IsIntegrallyClosed (D.presheaf.stalk e) :=
    IsIntegrallyClosed.of_equiv (pointClosureStalkEquiv d.1 e h)
  obtain ⟨e', rfl⟩ := νD.surjective e
  have hbijD : Function.Bijective (νD.stalkMap e').hom :=
    stalkMap_bijective_of_isIntegrallyClosed νD e'
  have he'1 : Order.coheight e' = 1 :=
    (coheight_eq_of_stalkMap_bijective νD e' hbijD).trans he1
  -- the point of `Aν`
  let Q' := qν e'
  have hpt : νA Q' = qD (νD e') := by
    change (qν ≫ νA) e' = _
    rw [hqν]
    rfl
  have hQeq : qD (νD e') = Q.1 := by
    apply ιA.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hqD, Scheme.Hom.comp_apply, hQ]
  haveI : IsIntegrallyClosed (A.presheaf.stalk Q.1) :=
    IsIntegrallyClosed.of_equiv
      (pointClosureStalkEquiv' (β d.1) Q.1 hQ (h.map β.continuous))
  haveI : IsIntegrallyClosed (A.presheaf.stalk (νA Q')) := by
    rw [hpt, hQeq]
    infer_instance
  have hbijA : Function.Bijective (νA.stalkMap Q').hom :=
    stalkMap_bijective_of_isIntegrallyClosed νA Q'
  have hQ'1 : Order.coheight Q' = 1 := by
    rw [coheight_eq_of_stalkMap_bijective νA Q' hbijA, hpt, hQeq]
    exact Q.2
  have hQ'U : Q' ∈ Uo := by
    by_contra hn
    apply hES
    exact ⟨Q.1, ⟨⟨Q', hn, hpt.trans hQeq⟩, Q.2⟩, hQ⟩
  have hb := hfib ⟨e', he'1⟩ ⟨Q', hQ'1⟩ rfl hQ'U
  rw [← hb]
  have hE : ιA (νA Q') = β (ιD (νD e')) := by
    rw [hpt, ← Scheme.Hom.comp_apply, hqD]
    rfl
  let eA : closureStalk X (h.map β.continuous) ≃+* Aν.presheaf.stalk Q' :=
    (pointClosureStalkEquiv' (β d.1) (νA Q') hE (h.map β.continuous)).trans
      (RingEquiv.ofBijective _ hbijA)
  let eB : closureStalk Y h ≃+* Dν.presheaf.stalk e' :=
    (pointClosureStalkEquiv d.1 (νD e') h).trans (RingEquiv.ofBijective _ hbijD)
  unfold closureFibreMultiplicity schemeDivisorRamificationIdx
  refine ramificationIdx_maximalIdeal_eq_of_square (stalkGenerizationQuotientMap β h)
    (qν.stalkMap e').hom eA eB fun a => ?_
  change (νD.stalkMap e').hom (pointClosureStalkEquiv d.1 (νD e') h
      (stalkGenerizationQuotientMap β h a)) =
    (qν.stalkMap e').hom ((νA.stalkMap Q').hom
      (pointClosureStalkEquiv' (β d.1) (νA Q') hE (h.map β.continuous) a))
  rw [← pointClosureStalkEquiv_naturality d.1 β (νD e') h a]
  set x := pointClosureStalkEquiv' (β d.1) (νA Q') hE (h.map β.continuous) a
  have h1 : (qν.stalkMap e').hom ((νA.stalkMap Q').hom x) = ((qν ≫ νA).stalkMap e').hom x := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have h2 : ((qν ≫ νA).stalkMap e').hom x =
      (ψ.stalkMap e').hom ((A.presheaf.stalkCongr (.of_eq hpt)).hom x) := by
    rw [Scheme.Hom.stalkMap_congr_hom (qν ≫ νA) ψ hqν e']
    rfl
  have h3 : (A.presheaf.stalkCongr (.of_eq hpt)).hom x =
      pointClosureStalkEquiv' (β d.1) (qD (νD e'))
        (by rw [← Scheme.Hom.comp_apply, hqD]; rfl) (h.map β.continuous) a :=
    pointClosureStalkEquiv'_congr (β d.1) hpt hE _ (h.map β.continuous) a
  have h4 (y : A.presheaf.stalk (qD (νD e'))) :
      (ψ.stalkMap e').hom y = (νD.stalkMap e').hom ((qD.stalkMap (νD e')).hom y) := by
    rw [Scheme.Hom.stalkMap_comp νD qD e']
    rfl
  rw [h1, h2, h3, h4]
#print axioms exists_finite_primary_bad_charZero

end
end Pcf
