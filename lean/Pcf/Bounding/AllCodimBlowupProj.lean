/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRees
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Affine cone and localized-chart precursors to the blow-up comparison

The first paragraph of `latex/paper-p.tex`, proof of Theorem
`thm:allcodim-normal`, uses a closed immersion from the blow-up of a pulled-back
ideal into the base change of the original blow-up (Stacks Tag 080E).
`AllCodimBlowupRees` proves the corresponding canonical Rees-algebra
base-change map is surjective. Here we pass that proven surjection to actual
scheme morphisms of affine Rees cones and of their principal localizations at
degree-one generators.

These are algebraic precursors. Mathlib's current `reesAlgebra` has no graded-ring
instance, so this file does not construct `Proj` itself. The blow-up is Mathlib's
`Proj` of the grading `reesGrade`, defined as `reesProj` in
`AllCodimBlowupProjChart.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped TensorProduct

namespace Pcf.Bounding.AllCodimBlowup

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual affine-cone scheme morphism induced by the canonical
base-change map of Rees rings. -/
def affineReesConeBaseChange (I : Ideal R) :
    Spec (.of (reesAlgebra (I.map (algebraMap R S)))) ⟶
      Spec (.of (S ⊗[R] reesAlgebra I)) :=
  Spec.map (CommRingCat.ofHom
    (reesAlgebraBaseChange (R := R) (S := S) I).toRingHom)

/-- Surjectivity of the base-change Rees map makes the corresponding affine
Rees-cone morphism a closed immersion. This is the affine-scheme part of the
closed-immersion claim before passing to Proj. -/
instance affineReesConeBaseChange_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion (affineReesConeBaseChange (S := S) I) := by
  unfold affineReesConeBaseChange
  exact IsClosedImmersion.spec_of_surjective _
    (reesAlgebraBaseChange_surjective (R := R) (S := S) I)

/-- The degree-one Rees generator of `a ∈ I`, placed on the base-changed
source cone. -/
def baseChangeDegreeOne (I : Ideal R) (a : I) :
    S ⊗[R] reesAlgebra I :=
  (1 : S) ⊗ₜ[R]
    (⟨monomial 1 a.1, reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using a.2)⟩ :
      reesAlgebra I)

/-- On the target Rees cone, the base-changed degree-one generator is exactly
`f(a)t`; it is not merely a generator up to radical. -/
@[simp] theorem reesAlgebraBaseChange_degreeOne (I : Ideal R) (a : I) :
    reesAlgebraBaseChange (R := R) (S := S) I
      (baseChangeDegreeOne (S := S) I a) =
      (⟨monomial 1 ((algebraMap R S) a.1),
        reesAlgebra.monomial_mem.mpr (by
          simpa using Ideal.mem_map_of_mem (algebraMap R S) a.2)⟩ :
        reesAlgebra (I.map (algebraMap R S))) := by
  simp [baseChangeDegreeOne, reesAlgebraBaseChange_tmul,
    reesAlgebraMap_monomial]

/-- The ring map on principal localizations of the two affine Rees cones
at a degree-one generator. These are the localization rings underlying the
standard `D_+(a t)` charts; the degree-zero parts are not constructed here. -/
def localizedReesBaseChange (I : Ideal R) (a : I) :
    Localization.Away (baseChangeDegreeOne (S := S) I a) →+*
      Localization.Away ((reesAlgebraBaseChange (R := R) (S := S) I).toRingHom
        (baseChangeDegreeOne (S := S) I a)) :=
  Localization.awayMap (reesAlgebraBaseChange (R := R) (S := S) I).toRingHom
    (baseChangeDegreeOne (S := S) I a)

/-- The localized Rees map remains surjective at every degree-one generator. -/
theorem localizedReesBaseChange_surjective (I : Ideal R) (a : I) :
    Function.Surjective (localizedReesBaseChange (S := S) I a) := by
  unfold localizedReesBaseChange
  exact IsLocalization.map_surjective_of_surjective _ _ _
    (reesAlgebraBaseChange_surjective (R := R) (S := S) I)

/-- Morphism of the affine schemes obtained by localizing both Rees cones
at corresponding degree-one generators. -/
def localizedReesConeBaseChange (I : Ideal R) (a : I) :
    Spec (.of (Localization.Away
      ((reesAlgebraBaseChange (R := R) (S := S) I).toRingHom
        (baseChangeDegreeOne (S := S) I a)))) ⟶
      Spec (.of (Localization.Away (baseChangeDegreeOne (S := S) I a))) :=
  Spec.map (CommRingCat.ofHom (localizedReesBaseChange (S := S) I a))

/-- Closed immersion of the affine schemes obtained by localizing both Rees
cones at the corresponding degree-one generators. -/
instance localizedReesConeBaseChange_isClosedImmersion (I : Ideal R) (a : I) :
    IsClosedImmersion (localizedReesConeBaseChange (S := S) I a) := by
  unfold localizedReesConeBaseChange
  exact IsClosedImmersion.spec_of_surjective _
    (localizedReesBaseChange_surjective (S := S) I a)

end

end Pcf.Bounding.AllCodimBlowup
