/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBadFinite
public import Pcf.Bounding.AllCodimBadFinitePrimaryCharZero
public import Pcf.Bounding.AllCodimCharZero
public import Pcf.Bounding.AllCodimCoreGood
public import Pcf.Bounding.AllCodimBlowupExceptionalComponents
public import Pcf.Bounding.AllCodimCoreAssembly
public import Pcf.Bounding.AllCodimBlowupExceptionalSurjectivity

/-!
# Finiteness of the bad set in characteristic zero (L2)

The characteristic-zero form of `allCodimBadFinite`. The argument is the same;
the fibre-multiplicity input is the characteristic-zero form of
`lem:primary-fibres` (multiplicity one off a finite set).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Pcf.Bounding.AllCodimBlowup

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- **L2** in characteristic zero. -/
theorem allCodimBadFiniteCharZero (k : Type u) [Field k] [CharZero k] :
    AllCodimBadFiniteCharZero k := by
  intro X _ _ _ _ s _ y hy B hB U _ hyU a ha
  let R := Γ(X, U)
  let P := allCodimCentrePrime U y hyU
  letI : Algebra k R :=
    ((s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  haveI : Algebra.FiniteType k R := by
    apply RingHom.finiteType_algebraMap.mp
    change ((s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  have hPfg : P.FG := IsNoetherian.noetherian P
  letI : IsIntegral (reesProj P) := reesProj_isIntegral P a ha
  let Y := Palomar.normalization (reesProj P)
  let β' : Y ⟶ X := allCodimBlowupToAmbient U y hyU a ha
  haveI : NoetherianSpace Y := normalizedReesProj_noetherianSpace k P hPfg a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj P)) :=
    reesProj_absoluteNormalizationMap_isFinite k P hPfg a ha
  letI : IsProper (reesProjToSpec P) := reesProjToSpec_isProper P hPfg
  haveI : LocallyOfFiniteType (β' ≫ s) := by
    change LocallyOfFiniteType ((Palomar.normalizationMap (reesProj P) ≫ reesProjToSpec P) ≫
      U.2.fromSpec ≫ s)
    haveI : LocallyOfFiniteType (reesProjToSpec P) := inferInstance
    haveI : LocallyOfFiniteType (Palomar.normalizationMap (reesProj P)) := inferInstance
    haveI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    haveI : LocallyOfFiniteType U.2.fromSpec := locallyOfFiniteType_of_isOpenImmersion _
    infer_instance
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (β' ≫ s)
  -- generic points
  haveI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hgX : genericPoint X ∈ (U : X.Opens) :=
    ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr ⟨y, trivial, hyU⟩
  have hfromη : U.2.fromSpec (genericPoint (Spec R)) = genericPoint X := by
    rw [← U.2.primeIdealOf_genericPoint]
    exact U.2.fromSpec_primeIdealOf ⟨_, hgX⟩
  haveI : IsDominant (normalizedReesProjToSpec P a ha) := normalizedReesProjToSpec_isDominant P a ha
  have hβη : β' (genericPoint Y) = genericPoint X := by
    change U.2.fromSpec (normalizedReesProjToSpec P a ha (genericPoint Y)) = _
    rw [map_genericPoint_eq_of_isDominant]
    exact hfromη
  have hyη : genericPoint X ∉ closure ({y} : Set X) := by
    intro hmem
    have h1 : y ⤳ genericPoint X := specializes_iff_mem_closure.mpr hmem
    have h2 : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
    exact hy (Specializes.antisymm h1 h2).eq
  have hDom : {w : Y | w ∈ β' ⁻¹' closure ({y} : Set X) ∧ Order.coheight w = 1}.Finite :=
    finite_coheight_one_of_isClosed _ (isClosed_closure.preimage β'.continuous)
      (by simpa [Set.mem_preimage, hβη] using hyη)
  have hgenW : ∀ w : Y, Order.coheight w = 1 → β' w ≠ genericPoint X := by
    intro w hw heq
    let βR := normalizedReesProjToSpec P a ha
    have hβR : βR w = genericPoint (Spec R) := by
      apply U.2.fromSpec.isOpenEmbedding.injective
      exact heq.trans hfromη.symm
    have hbot : (βR w).asIdeal = ⊥ := by
      rw [hβR, genericPoint_eq_bot_of_affine R]
      rfl
    have hbij := normalizedReesToSpec_stalkMap_bijective P a ha w (by
      change ¬ P ≤ (βR w).asIdeal
      rw [hbot]
      exact fun hle => allCodimCentrePrime_ne_bot U y hyU hy (le_bot_iff.mp hle))
    have hco := coheight_eq_of_stalkMap_bijective _ w hbij
    change Order.coheight w = Order.coheight (βR w) at hco
    rw [hβR, hw] at hco
    have h0 : Order.coheight (genericPoint (Spec R)) = 0 := by
      rw [Order.coheight_eq_zero]
      intro z _
      exact (genericPoint_spec (Spec R)).specializes (Set.mem_univ z)
    rw [h0] at hco
    exact one_ne_zero hco
  -- the finite set of divisors meeting the exceptional or postcritical loci
  let Cset : Set X := closure ({y} : Set X) ∪ ⋃ b ∈ B \ {genericPoint X}, closure ({b} : Set X)
  have hCcl : IsClosed Cset :=
    isClosed_closure.union ((hB.sdiff).isClosed_biUnion fun _ _ => isClosed_closure)
  have hCη : genericPoint X ∉ Cset := by
    rintro (h | h)
    · exact hyη h
    · obtain ⟨b, ⟨hbB, hbη⟩, hb⟩ := Set.mem_iUnion₂.mp h
      have h1 : b ⤳ genericPoint X := specializes_iff_mem_closure.mpr hb
      have h2 : genericPoint X ⤳ b := (genericPoint_spec X).specializes trivial
      exact hbη (Specializes.antisymm h1 h2).eq
  have hW : {w : Y | Order.coheight w = 1 ∧ (y ⤳ β' w ∨ β' w ∈ B)}.Finite := by
    refine (finite_coheight_one_of_isClosed (β' ⁻¹' Cset) (hCcl.preimage β'.continuous)
      (by simpa [Set.mem_preimage, hβη] using hCη)).subset ?_
    rintro w ⟨hw1, hw | hw⟩
    · exact ⟨Or.inl (specializes_iff_mem_closure.mp hw), hw1⟩
    · refine ⟨Or.inr (Set.mem_iUnion₂.mpr ⟨β' w, ⟨hw, hgenW w hw1⟩, subset_closure rfl⟩), hw1⟩
  -- non-normal points of `A`
  let A := (pointClosureIdealSheaf y).subscheme
  let ιA : A ⟶ X := (pointClosureIdealSheaf y).subschemeι
  haveI : LocallyOfFiniteType (ιA ≫ s) := inferInstance
  have hSa := (finite_nonNormal_schemeDivisorPoint k (ιA ≫ s)).image fun Q => ιA Q.1
  -- per dominating divisor
  have hper : ∀ w ∈ {w : Y | w ∈ β' ⁻¹' closure ({y} : Set X) ∧ Order.coheight w = 1},
      ∃ S : Set X, S.Finite ∧ ∀ (hw1 : Order.coheight w = 1) (hβw : β' w = y),
        (β' '' {E : Y | ∃ h : w ⤳ E, Order.coheight E = 2 ∧
          ¬ ((stalkGenerizationPrime Y h).IsPrincipal ∧
            IsDiscreteValuationRing (closureStalk Y h) ∧
            ∀ w' : SchemeDivisorPoint Y, w'.1 ⤳ E → w' ≠ ⟨w, hw1⟩ →
              ¬ y ⤳ β' w'.1 ∧ β' w'.1 ∉ B)}) ⊆ S ∧
        ∀ (E : Y) (h : w ⤳ E), Order.coheight E = 2 →
          IsDiscreteValuationRing (closureStalk Y h) →
          (∃ Q : SchemeDivisorPoint A, ιA Q.1 = β' E) →
          IsDiscreteValuationRing (closureStalk X (h.map β'.continuous)) →
          β' E ∉ S → ∃ b : ℕ, closureFibreMultiplicity β' h = 1 ^ b := by
    rintro w ⟨-, hw1⟩
    let d : SchemeDivisorPoint Y := ⟨w, hw1⟩
    have hbadE := finite_bad_exceptional_points k (β' ≫ s) β' y B d hW
    by_cases hβw : β' w = y
    · obtain ⟨S1, hS1, hprim⟩ := exists_finite_primary_bad_charZero k s β' y d hβw
      refine ⟨β' '' _ ∪ S1, (hbadE.image β').union hS1, fun _ _ => ⟨Set.subset_union_left, ?_⟩⟩
      intro E h hE2 hDdvr hQ hXdvr hES
      exact ⟨0, (hprim E h hE2 hDdvr hQ hXdvr fun hm => hES (Or.inr hm)).trans
        (pow_zero 1).symm⟩
    · exact ⟨∅, Set.finite_empty, fun _ hβw' => absurd hβw' hβw⟩
  choose! Sf hSf_fin hSf using hper
  refine (hSa.union (hDom.biUnion hSf_fin)).subset ?_
  rintro x ⟨⟨Q, hQx⟩, hxU, hbad⟩
  by_contra hx
  apply hbad
  have hyx : y ⤳ x := hQx ▸ pointClosure_specializes y Q.1
  haveI : IsIntegrallyClosed (A.presheaf.stalk Q.1) := by
    by_contra hn
    exact hx (Or.inl ⟨Q, hn, hQx⟩)
  have hAdvr : IsDiscreteValuationRing (closureStalk X hyx) :=
    closureStalk_dvr_of_isIntegrallyClosed y Q hQx hyx
  refine ⟨hyx, hAdvr, ?_⟩
  intro d hβd E hdE hβE hcoh
  have hdDom : d.1 ∈ {w : Y | w ∈ β' ⁻¹' closure ({y} : Set X) ∧ Order.coheight w = 1} :=
    ⟨by
      change β' d.1 ∈ closure ({y} : Set X)
      rw [hβd]
      exact subset_closure rfl, d.2⟩
  obtain ⟨hsub, hprim⟩ := hSf d.1 hdDom d.2 hβd
  have hxS : x ∉ Sf d.1 := fun hm => hx (Or.inr (Set.mem_biUnion hdDom hm))
  by_contra hng
  have h3 : (stalkGenerizationPrime Y hdE).IsPrincipal ∧
      IsDiscreteValuationRing (closureStalk Y hdE) ∧
      ∀ w' : SchemeDivisorPoint Y, w'.1 ⤳ E → w' ≠ d → ¬ y ⤳ β' w'.1 ∧ β' w'.1 ∉ B := by
    by_contra hn
    apply hxS
    rw [← hβE]
    exact hsub ⟨E, ⟨hdE, hcoh, hn⟩, rfl⟩
  obtain ⟨hpr, hdv, hiso⟩ := h3
  apply hng
  refine ⟨hpr, hdv, hiso, ?_⟩
  exact hprim E hdE hcoh hdv ⟨Q, hQx.trans hβE.symm⟩
    (closureStalk_dvr_congr hβd.symm hβE.symm hyx (hdE.map β'.continuous) hAdvr)
    (by rw [hβE]; exact hxS)

#print axioms allCodimBadFiniteCharZero

end
end Pcf
