/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupExceptionalNaturality
public import Pcf.Bounding.AllCodimBlowupNormalizedExceptionalChart

/-!
# The exceptional ideal under a finite normalized Rees lift

The finite normalized Rees map identifies the pullback of the actual
exceptional ideal sheaf with the exceptional ideal sheaf of the extended
centre. This strengthens the earlier equality of supports and retains the
scheme-theoretic multiplicities needed in `paper-p.tex`, Theorem
`thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Extension of an affine centre ideal commutes with pullback along an
actual morphism of affine spectra. -/
theorem affineCenterIdealSheaf_comap_specMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    (affineCenterIdealSheaf I).comap (Spec.map (CommRingCat.ofHom f)) =
      affineCenterIdealSheaf (I.map f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [ideal_comap_affine, affineCenterIdealSheaf_ideal_top,
    affineCenterIdealSheaf_ideal_top, Ideal.map_map, Ideal.map_map]
  exact congrArg (fun h : R →+* Γ(Spec (.of S), ⊤) => I.map h)
    (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

/-- The finite map of normalized Rees blow-ups pulls back the actual
exceptional *ideal sheaf*, including its scheme-theoretic multiplicity. -/
theorem normalizedReesExceptionalIdealSheaf_comap
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    (normalizedReesExceptionalIdealSheaf I a ha).comap
        (normalizedReesProjMap f hf hfin I a ha) =
      normalizedReesExceptionalIdealSheaf (I.map f) b hb := by
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
      _ = νS ≫ βS ≫ Spec.map (CommRingCat.ofHom f) := by rfl
  dsimp only [normalizedReesExceptionalIdealSheaf, reesExceptionalIdealSheaf]
  simp only [← Scheme.IdealSheafData.comap_comp]
  rw [hsquare]
  simp only [Scheme.IdealSheafData.comap_comp,
    affineCenterIdealSheaf_comap_specMap]
  rfl

#print axioms affineCenterIdealSheaf_comap_specMap
#print axioms normalizedReesExceptionalIdealSheaf_comap

end
end Pcf.Bounding.AllCodimBlowup
