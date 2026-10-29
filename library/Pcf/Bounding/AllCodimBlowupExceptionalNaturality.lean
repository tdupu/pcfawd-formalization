/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupNormalizedExceptional
public import Pcf.Bounding.AllCodimBlowupNormalizedLift
public import Pcf.Bounding.AllCodimBlowupGenericStalkNaturality

/-!
# Exceptional support under the finite normalized Rees lift

The normalized finite Rees map pulls the full exceptional support of
the target centre back to the full exceptional support of the mapped
centre. This uses the actual ideal sheaves, the normalized Rees square,
and the exact zero-locus identity for the mapped centre.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {R S : Type u} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S]

omit [IsDomain R] [IsDomain S] in
/-- The source centre is exactly the inverse image of the target centre
under the affine map induced by the coefficient homomorphism. -/
theorem mappedCenter_zeroLocus_preimage (f : R →+* S) (I : Ideal R) :
    (Spec.map (CommRingCat.ofHom f)).base ⁻¹'
      PrimeSpectrum.zeroLocus (I : Set R) =
        PrimeSpectrum.zeroLocus ((I.map f) : Set S) := by
  change (PrimeSpectrum.comap f) ⁻¹'
    PrimeSpectrum.zeroLocus (I : Set R) = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus]
  rw [Ideal.map, PrimeSpectrum.zeroLocus_span]

/-- The finite map between actual absolute normalized Rees blow-ups
pulls back the whole exceptional support, including every component
over the centre. -/
theorem normalizedReesExceptional_support_preimage
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    (normalizedReesProjMap f hf hfin I a ha).base ⁻¹'
      ((normalizedReesExceptionalIdealSheaf I a ha).support :
        Set (Palomar.normalization (reesProj I))) =
      ((normalizedReesExceptionalIdealSheaf (I.map f) b hb).support :
        Set (Palomar.normalization (reesProj (I.map f)))) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let g := normalizedReesProjMap f hf hfin I a ha
  let νR := Palomar.normalizationMap (reesProj I)
  let νS := Palomar.normalizationMap (reesProj (I.map f))
  let βR := reesProjToSpec I
  let βS := reesProjToSpec (I.map f)
  have hsquare : g ≫ νR ≫ βR =
      νS ≫ βS ≫ Spec.map (CommRingCat.ofHom f) := by
    calc
      g ≫ νR ≫ βR = (νS ≫ reesProjMap f I) ≫ βR := by
        simpa only [g, νR, νS, Category.assoc] using
          congrArg (fun h : Palomar.normalization (reesProj (I.map f)) ⟶
            reesProj I => h ≫ βR)
            (normalizedReesProjMap_comm f hf hfin I a ha)
      _ = νS ≫ (reesProjMap f I ≫ βR) := by simp only [Category.assoc]
      _ = νS ≫ (βS ≫ Spec.map (CommRingCat.ofHom f)) := by
        rw [reesProjMap_toSpec f I]
      _ = νS ≫ βS ≫ Spec.map (CommRingCat.ofHom f) := by
        rfl
  dsimp only
  rw [normalizedReesExceptionalIdealSheaf_support,
    normalizedReesExceptionalIdealSheaf_support]
  ext x
  change (βR (νR (g x))) ∈ PrimeSpectrum.zeroLocus (I : Set R) ↔
    (βS (νS x)) ∈ PrimeSpectrum.zeroLocus ((I.map f) : Set S)
  have hpoint : βR (νR (g x)) =
      (Spec.map (CommRingCat.ofHom f)) (βS (νS x)) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun h : Palomar.normalization (reesProj (I.map f)) ⟶ Spec (.of R) =>
        h x) hsquare
  rw [hpoint]
  exact Set.ext_iff.mp (mappedCenter_zeroLocus_preimage f I) (βS (νS x))

#print axioms mappedCenter_zeroLocus_preimage
#print axioms normalizedReesExceptional_support_preimage

end
end Pcf.Bounding.AllCodimBlowup
