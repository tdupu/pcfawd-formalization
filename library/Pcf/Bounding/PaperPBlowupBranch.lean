/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupIsoOffCentre
public import Pcf.Bounding.AllCodimBlowupExceptionalNaturality
public import Pcf.Bounding.AllCodimBlowupMonodromyTransport

/-!
# Branch support of an affine normalized blow-up outside the centre

This is the stalk comparison in `paper-p.tex`, Proposition
`prop:normalized-blowup-branch`. It applies to the actual finite map
between normalized Rees blow-ups of an affine finite map.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- Away from the exceptional divisor, formal étaleness of the finite
normalized Rees map is equivalent to formal étaleness of the original
finite affine map at the corresponding source point. -/
theorem normalizedReesProjMap_formallyEtale_iff_offCentre
    {R S : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (w : (let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
      Palomar.normalization (reesProj (I.map f))))
    (hw : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
      ¬ (normalizedReesProjMap f hf hfin I a ha w) ∈
        (normalizedReesExceptionalIdealSheaf I a ha).support)) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
    let g := normalizedReesProjMap f hf hfin I a ha
    let α := normalizedReesProjToSpec (I.map f) b hb
    (g.stalkMap w).hom.FormallyEtale ↔
      ((Spec.map (CommRingCat.ofHom f)).stalkMap (α w)).hom.FormallyEtale := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  let g := normalizedReesProjMap f hf hfin I a ha
  let β := normalizedReesProjToSpec I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  dsimp only at hw
  have hβoff : ¬ I ≤ (β (g w)).asIdeal := by
    intro h
    apply hw
    have hsupport := normalizedReesExceptionalIdealSheaf_support I a ha
    have hiff := Set.ext_iff.mp hsupport (g w)
    exact hiff.mpr ((PrimeSpectrum.mem_zeroLocus _ _).mpr h)
  have hαoff : ¬ I.map f ≤ (α w).asIdeal := by
    have hpre := normalizedReesExceptional_support_preimage f hf hfin I a ha
    have hw' : w ∉ (normalizedReesExceptionalIdealSheaf (I.map f) b hb).support := by
      dsimp only at hpre
      have hiff := Set.ext_iff.mp hpre w
      exact fun h => hw (hiff.mpr h)
    intro h
    apply hw'
    have hsupport := normalizedReesExceptionalIdealSheaf_support (I.map f) b hb
    have hiff := Set.ext_iff.mp hsupport w
    exact hiff.mpr ((PrimeSpectrum.mem_zeroLocus _ _).mpr h)
  have hβ : Function.Bijective (β.stalkMap (g w)).hom :=
    normalizedReesToSpec_stalkMap_bijective I a ha (g w) hβoff
  have hα : Function.Bijective (α.stalkMap w).hom :=
    normalizedReesToSpec_stalkMap_bijective (I.map f) b hb w hαoff
  exact formallyEtale_stalkMap_iff_of_square g α β
    (Spec.map (CommRingCat.ofHom f))
    (normalizedReesProjToSpec_comm f hf hfin I a ha) w hα hβ

/-- A codimension-one branch point of the actual lifted finite map away from
the exceptional divisor lies over a codimension-one branch point of the
original affine finite map. This is the off-centre part of
`prop:normalized-blowup-branch` in `paper-p.tex`. -/
theorem normalizedReesProjMap_branch_offCentre
    {R S : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (w : (let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
      Palomar.normalization (reesProj (I.map f))))
    (hcodim : Order.coheight w = 1)
    (hw : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
      ¬ (normalizedReesProjMap f hf hfin I a ha w) ∈
        (normalizedReesExceptionalIdealSheaf I a ha).support))
    (hbranch : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
      ¬ ((normalizedReesProjMap f hf hfin I a ha).stalkMap w).hom.FormallyEtale)) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
    let g := normalizedReesProjMap f hf hfin I a ha
    let β := normalizedReesProjToSpec I a ha
    let α := normalizedReesProjToSpec (I.map f) b hb
    ∃ d : SchemeDivisorPoint (Spec (CommRingCat.of S)),
      d.1 = α w ∧
      d ∈ schemeDivisorNonEtaleLocus (Spec.map (CommRingCat.ofHom f)) ∧
      β (g w) = (Spec.map (CommRingCat.ofHom f)) d.1 := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  let g := normalizedReesProjMap f hf hfin I a ha
  let β := normalizedReesProjToSpec I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  have hαoff : ¬ I.map f ≤ (α w).asIdeal := by
    have hpre := normalizedReesExceptional_support_preimage f hf hfin I a ha
    have hw' : w ∉ (normalizedReesExceptionalIdealSheaf (I.map f) b hb).support := by
      dsimp only at hpre hw
      have hiff := Set.ext_iff.mp hpre w
      exact fun h => hw (hiff.mpr h)
    intro h
    apply hw'
    have hsupport := normalizedReesExceptionalIdealSheaf_support (I.map f) b hb
    have hiff := Set.ext_iff.mp hsupport w
    exact hiff.mpr ((PrimeSpectrum.mem_zeroLocus _ _).mpr h)
  have hα : Function.Bijective (α.stalkMap w).hom :=
    normalizedReesToSpec_stalkMap_bijective (I.map f) b hb w hαoff
  let d : SchemeDivisorPoint (Spec (CommRingCat.of S)) :=
    ⟨α w, (coheight_eq_of_stalkMap_bijective α w hα).symm ▸ hcodim⟩
  refine ⟨d, rfl, ?_, ?_⟩
  · exact (normalizedReesProjMap_formallyEtale_iff_offCentre f hf hfin I a ha w hw).not.mp
      hbranch
  · have hcomm := normalizedReesProjToSpec_comm f hf hfin I a ha
    have hpoint := congrArg (fun m => m w) hcomm
    simpa only [Scheme.Hom.comp_apply] using hpoint

#print axioms normalizedReesProjMap_formallyEtale_iff_offCentre
#print axioms normalizedReesProjMap_branch_offCentre

end
end Pcf.Bounding.AllCodimBlowup
