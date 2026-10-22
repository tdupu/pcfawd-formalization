/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.InvariantDivisorGeometry

/-!
# Actual returns on point closures in every codimension

An integral closed subvariety of an integral scheme is the reduced closure of
its generic point.  These constructions use an arbitrary point of the original
scheme, rather than a codimension-one point or a normalization.  They supply
the geometric objects occurring in `paper-p.tex`, Definition
`def:pcfawd-allsubvar`.  No PCF conclusion is asserted here.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- Every reduced point closure is an integral scheme, in any codimension. -/
instance pointClosureSubscheme_integral {X : Scheme.{u}} (x : X) :
    IsIntegral (pointClosureIdealSheaf x).subscheme :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- On an integral scheme, the closure of a point is proper exactly when
the point is not the ambient generic point. -/
theorem pointClosure_proper_iff {X : Scheme.{u}} [IsIntegral X] (x : X) :
    closure ({x} : Set X) ≠ Set.univ ↔ x ≠ genericPoint X := by
  constructor
  · intro h hx
    subst x
    exact h (genericPoint_spec X)
  · intro h hx
    exact h ((show IsGenericPoint x (Set.univ : Set X) from hx).eq
      (genericPoint_spec X))

/-- A point representing a proper integral reduced closed subvariety of
an integral scheme. Its actual scheme is `pointClosureIdealSheaf x`. -/
def ProperIntegralSubvarietyPoint (X : Scheme.{u}) [IsIntegral X] :=
  {x : X // x ≠ genericPoint X}

/-- The point representing the image of an integral closed subvariety under
the `r`-th iterate of a self-map. -/
def schemePointIterate {X : Scheme.{u}} (f : X ⟶ X) (r : ℕ) (x : X) : X :=
  (End.of f ^ r).asHom.base x

/-- A preperiodicity relation on a point makes its image point periodic under
the stated return time. -/
theorem schemePointIterate_periodic {X : Scheme.{u}} (f : X ⟶ X)
    (r s : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    (End.of f ^ s).asHom.base (schemePointIterate f r x) =
      schemePointIterate f r x := by
  unfold schemePointIterate at h ⊢
  rw [Nat.add_comm r s, pow_add] at h
  exact h

/-- The actual return map on the original reduced point closure, with no
normalization or codimension restriction. -/
def pointClosureReturnMap {X : Scheme.{u}} (f : X ⟶ X)
    (x : X) (h : f x = x) :
    (pointClosureIdealSheaf x).subscheme ⟶
      (pointClosureIdealSheaf x).subscheme :=
  pointClosureSubschemeMap f x x h

/-- A finite self-map has a finite return map on an invariant reduced point
closure, in any codimension. -/
instance pointClosureReturnMap_isFinite {X : Scheme.{u}}
    (f : X ⟶ X) [IsFinite f] (x : X) (h : f x = x) :
    IsFinite (pointClosureReturnMap f x h) :=
  pointClosureSubschemeMap_isFinite f x x h

/-- The return map on an invariant reduced point closure is dominant. -/
instance pointClosureReturnMap_isDominant {X : Scheme.{u}}
    (f : X ⟶ X) (x : X) (h : f x = x) :
    IsDominant (pointClosureReturnMap f x h) :=
  pointClosureSubschemeMap_isDominant f x x h

/-- A finite return on an invariant reduced point closure is surjective. -/
theorem pointClosureReturnMap_surjective {X : Scheme.{u}}
    (f : X ⟶ X) [IsFinite f] (x : X) (h : f x = x) :
    Function.Surjective (pointClosureReturnMap f x h) :=
  pointClosureSubschemeMap_surjective f x x h

/-- Over a locally Noetherian ambient scheme, a finite point-closure return
is locally of finite presentation. -/
instance pointClosureReturnMap_locallyOfFinitePresentation {X : Scheme.{u}}
    (f : X ⟶ X) [IsFinite f] [IsLocallyNoetherian X]
    (x : X) (h : f x = x) :
    LocallyOfFinitePresentation (pointClosureReturnMap f x h) := by
  infer_instance

/-- An iterate of the return on the original reduced closure is the
restriction of the ambient iterate. -/
theorem pointClosureReturnMap_iterate {X : Scheme.{u}}
    (f : X ⟶ X) (x : X) (h : f x = x) (m : ℕ) :
    (End.of (pointClosureReturnMap f x h) ^ m).asHom =
      pointClosureReturnMap (End.of f ^ m).asHom x
        (end_pow_apply_eq_of_apply_eq f x h m) :=
  pointClosureSubschemeMap_iterate f x h m

/-- The return on the image of an eventually periodic point is an actual
finite dominant map between integral schemes. -/
def eventuallyPeriodicPointReturn {X : Scheme.{u}}
    (f : X ⟶ X) (r s : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    (pointClosureIdealSheaf (schemePointIterate f r x)).subscheme ⟶
      (pointClosureIdealSheaf (schemePointIterate f r x)).subscheme :=
  pointClosureReturnMap (End.of f ^ s).asHom
    (schemePointIterate f r x) (schemePointIterate_periodic f r s x h)

instance eventuallyPeriodicPointReturn_isFinite {X : Scheme.{u}}
    (f : X ⟶ X) [IsFinite f] (r s : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    IsFinite (eventuallyPeriodicPointReturn f r s x h) := by
  unfold eventuallyPeriodicPointReturn
  letI : IsFinite (End.of f ^ s).asHom := isFinite_end_pow f s
  infer_instance

instance eventuallyPeriodicPointReturn_isDominant {X : Scheme.{u}}
    (f : X ⟶ X) (r s : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    IsDominant (eventuallyPeriodicPointReturn f r s x h) := by
  unfold eventuallyPeriodicPointReturn
  infer_instance

/-- The return on the periodic image of a point is surjective. -/
theorem eventuallyPeriodicPointReturn_surjective {X : Scheme.{u}}
    (f : X ⟶ X) [IsFinite f] (r s : ℕ) (x : X)
    (h : schemePointIterate f (r + s) x = schemePointIterate f r x) :
    Function.Surjective (eventuallyPeriodicPointReturn f r s x h) := by
  unfold eventuallyPeriodicPointReturn
  letI : IsFinite (End.of f ^ s).asHom := isFinite_end_pow f s
  exact pointClosureReturnMap_surjective _ _ _

#print axioms pointClosureSubscheme_integral
#print axioms pointClosure_proper_iff
#print axioms schemePointIterate_periodic
#print axioms pointClosureReturnMap_iterate
#print axioms eventuallyPeriodicPointReturn_isFinite
#print axioms eventuallyPeriodicPointReturn_isDominant
#print axioms eventuallyPeriodicPointReturn_surjective

end

end Pcf
