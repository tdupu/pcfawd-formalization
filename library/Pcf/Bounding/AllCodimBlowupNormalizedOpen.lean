/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupIdealTransport
public import Pcf.Bounding.AllCodimBlowupOpenBaseChange
public import Pcf.Bounding.AbsoluteNormalizationOpenBaseChange

/-!
# Normalized Rees transitions for affine open coefficient change

Unlike the finite-map normalization lift, this construction requires no finite
coefficient map. It uses the actual absolute-normalization open comparison.
The domain and nonzero-centre restrictions come from the current Rees
Cartesian base-change theorem, not from normalization.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- The actual Cartesian comparison persists after identifying the extended
ideal with the ideal attached to a smaller affine open.

**Divergence from Stacks 0805:** restricted to domain coefficient rings, an
injective map inducing an open immersion, and a nonzero centre. -/
@[stacks 0805 "integral affine open-immersion case; specified equal extended ideal"]
theorem reesProjMapTo_isPullback_of_openImmersion
    (f : R →+* S) (hf : Function.Injective f)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (I : Ideal R) (J : Ideal S) (h : I.map f = J)
    (a : I) (ha : (a : R) ≠ 0) :
    IsPullback (reesProjToSpec J) (reesProjMapTo f I J h)
      (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I) := by
  subst J
  exact reesProjMap_isPullback_of_openImmersion f hf I a ha

variable (f : R →+* S) (hf : Function.Injective f)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
  (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)

/-- The actual normalization lift of an affine open Rees transition. -/
def normalizedReesProjOpenMap :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
        (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
    Palomar.normalization (reesProj (I.map f)) ⟶ Palomar.normalization (reesProj I) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
      (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
  letI := reesProjMap_isOpenImmersion_of_openImmersion f hf I a ha
  exact Pcf.absoluteNormalizationOpenMap (reesProjMap f I)

@[reassoc] theorem normalizedReesProjOpenMap_comm :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
        (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
    normalizedReesProjOpenMap f hf I a ha ≫ Palomar.normalizationMap (reesProj I) =
      Palomar.normalizationMap (reesProj (I.map f)) ≫ reesProjMap f I := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
      (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
  letI := reesProjMap_isOpenImmersion_of_openImmersion f hf I a ha
  exact Pcf.absoluteNormalizationOpenMap_comp (reesProjMap f I)

/-- Normalization of the integral Rees scheme commutes with this open
restriction, using the actual Cartesian inverse-image square.

**Divergence from Stacks 035K:** specialization to normalization in the generic
point of integral affine Rees schemes with a nonzero centre. -/
@[stacks 035K "integral affine Rees schemes; normalization in the generic point"]
theorem normalizedReesProjOpenMap_isPullback :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
        (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
    IsPullback (Palomar.normalizationMap (reesProj (I.map f)))
      (normalizedReesProjOpenMap f hf I a ha) (reesProjMap f I)
      (Palomar.normalizationMap (reesProj I)) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
      (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
  letI := reesProjMap_isOpenImmersion_of_openImmersion f hf I a ha
  exact Pcf.absoluteNormalizationOpen_isPullback (reesProjMap f I)

/-- The complete normalized Rees transition square over the affine bases. -/
theorem normalizedReesProjOpenMap_toSpec_isPullback :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
        (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
    IsPullback
      (Palomar.normalizationMap (reesProj (I.map f)) ≫ reesProjToSpec (I.map f))
      (normalizedReesProjOpenMap f hf I a ha)
      (Spec.map (CommRingCat.ofHom f))
      (Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
      (fun h ↦ ha (hf (by simpa [mappedCenterElement] using h)))
  exact (normalizedReesProjOpenMap_isPullback f hf I a ha).paste_horiz
    (reesProjMap_isPullback_of_openImmersion f hf I a ha)

#print axioms reesProjMapTo_isPullback_of_openImmersion
#print axioms normalizedReesProjOpenMap
#print axioms normalizedReesProjOpenMap_comm
#print axioms normalizedReesProjOpenMap_isPullback
#print axioms normalizedReesProjOpenMap_toSpec_isPullback
end
end Pcf.Bounding.AllCodimBlowup
