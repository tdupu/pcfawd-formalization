/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGenericStalk

/-!
# Generic-stalk naturality for Rees Proj maps

The Rees Proj square over a coefficient map is already global. Here it is
specialized to the generic points of the actual integral blow-ups. This is
the scheme-level naturality input for transporting the function-field
extension in `latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

noncomputable section

variable {R S : Type u} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S]

omit [IsDomain R] [IsDomain S] in
theorem mappedCenterElement_ne_zero (f : R →+* S)
    (hf : Function.Injective f) (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    ((mappedCenterElement f I a : I.map f) : S) ≠ 0 := by
  intro h
  exact ha (hf (by simpa [mappedCenterElement] using h))

/-- An injective coefficient map sends the source Rees Proj generic point
to the target Rees Proj generic point. -/
theorem reesProjMap_genericPoint (f : R →+* S)
    (hf : Function.Injective f) (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
        (mappedCenterElement_ne_zero f hf I a ha)
    reesProjMap f I (genericPoint (reesProj (I.map f))) =
      genericPoint (reesProj I) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
      (mappedCenterElement_ne_zero f hf I a ha)
  letI : IsDominant (reesProjMap f I) :=
    reesProjMap_isDominant_of_injective f hf I a ha
  exact map_genericPoint_eq_of_isDominant (reesProjMap f I)

omit [IsDomain R] in
/-- The global Rees Proj square induces the corresponding square of actual
generic stalk maps, with the canonical transport between equal base points. -/
theorem reesProjMap_genericStalk_square (f : R →+* S)
    (hf : Function.Injective f) (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
        (mappedCenterElement_ne_zero f hf I a ha)
    let η := genericPoint (reesProj (I.map f))
    let hpoint :
        (reesProjToSpec I) (reesProjMap f I η) =
          (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec (I.map f) η) :=
      congrArg (fun g : reesProj (I.map f) ⟶ Spec (.of R) => g η)
        (reesProjMap_toSpec f I)
    (reesProjToSpec I).stalkMap (reesProjMap f I η) ≫
        (reesProjMap f I).stalkMap η =
      ((Spec (.of R)).presheaf.stalkCongr (.of_eq hpoint)).hom ≫
        (Spec.map (CommRingCat.ofHom f)).stalkMap
          (reesProjToSpec (I.map f) η) ≫
        (reesProjToSpec (I.map f)).stalkMap η := by
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) (mappedCenterElement f I a)
      (mappedCenterElement_ne_zero f hf I a ha)
  let η := genericPoint (reesProj (I.map f))
  have h := Scheme.Hom.stalkMap_congr_hom
    (reesProjMap f I ≫ reesProjToSpec I)
    (reesProjToSpec (I.map f) ≫ Spec.map (CommRingCat.ofHom f))
    (reesProjMap_toSpec f I) η
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
  exact h

#print axioms reesProjMap_genericPoint
#print axioms reesProjMap_genericStalk_square

end

end Pcf.Bounding.AllCodimBlowup
