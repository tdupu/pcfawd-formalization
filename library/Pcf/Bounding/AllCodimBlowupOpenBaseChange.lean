/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeGluing
public import Pcf.Bounding.AllCodimBlowupNormalizedLift

/-!
# Rees blow-ups commute with affine open base change

For integral affine schemes and a nonzero centre, the relative Rees
comparison is an isomorphism whenever the coefficient map induces an
open immersion. This supplies Cartesian transition squares required by
relative gluing over an affine open cover of a nonaffine variety.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

set_option linter.style.haveILetI false

variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- The canonical relative Rees comparison is an isomorphism under an
injective coefficient map inducing an affine open immersion. The proof
uses its already proved closed immersion, dominance, and reducedness of
the open base change of the integral target blow-up. -/
theorem reesProjRelativeBaseChange_isIso_of_openImmersion
    (f : R →+* S) (hf : Function.Injective f)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    IsIso (reesProjRelativeBaseChange f I) := by
  letI : Algebra R S := f.toAlgebra
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let F := reesProjRelativeBaseChange f I
  let j := Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I)
  letI : IsOpenImmersion j := inferInstance
  letI : IsClosedImmersion F := reesProjRelativeBaseChange_isClosedImmersion I
  letI : IsDominant (F ≫ j) := by
    dsimp only [F, j]
    rw [reesProjRelativeBaseChange_snd]
    exact reesProjMap_isDominant_of_injective f hf I a ha
  letI : IsDominant F := IsDominant.of_comp_of_isOpenImmersion F j
  letI : IsReduced (Limits.pullback (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I)) :=
    isReduced_of_isOpenImmersion j
  letI : Surjective F :=
    surjective_of_isDominant_of_isClosed_range F F.isClosedMap.isClosed_range
  exact isIso_of_isClosedImmersion_of_surjective F

/-- The open coefficient change gives the Cartesian square required
for the transition maps of a relative gluing datum.

**Divergence from Stacks 0805:** this is the integral affine open-immersion
case of its flat base-change statement, with an injective coefficient map
and a nonzero centre. The full arbitrary flat base-change theorem is not
claimed here. -/
@[stacks 0805 "integral affine open-immersion case with nonzero centre"]
theorem reesProjMap_isPullback_of_openImmersion
    (f : R →+* S) (hf : Function.Injective f)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    IsPullback (reesProjToSpec (I.map f)) (reesProjMap f I)
      (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I) := by
  letI := reesProjRelativeBaseChange_isIso_of_openImmersion f hf I a ha
  exact IsPullback.of_iso_pullback ⟨(reesProjMap_toSpec f I).symm⟩
    (asIso (reesProjRelativeBaseChange f I))
    (reesProjRelativeBaseChange_fst f I) (reesProjRelativeBaseChange_snd f I)

/-- The transition map between the actual Rees blow-ups is an open
immersion, as the base change of the original affine open immersion. -/
theorem reesProjMap_isOpenImmersion_of_openImmersion
    (f : R →+* S) (hf : Function.Injective f)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    IsOpenImmersion (reesProjMap f I) := by
  letI := reesProjRelativeBaseChange_isIso_of_openImmersion f hf I a ha
  rw [← reesProjRelativeBaseChange_snd]
  infer_instance

#print axioms reesProjMap_isPullback_of_openImmersion
#print axioms reesProjMap_isOpenImmersion_of_openImmersion

#print axioms reesProjRelativeBaseChange_isIso_of_openImmersion

end
end Pcf.Bounding.AllCodimBlowup
