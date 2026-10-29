/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCentrePointClosureMonodromy
public import Pcf.Bounding.NormalizationLiftMonodromy
public import Pcf.Bounding.GlobalNormalizationFinite
public import Pcf.Bounding.SchemePrimeToPIteration
public import Pcf.Bounding.AllSubvarietyGeometry

/-!
# Monodromy of normalized returns on arbitrary point closures

The finite normalization of a reduced integral point closure is automatic
over a field. The actual return map and its canonical normalization lift
therefore inherit prime-to-characteristic monodromy from a finite ambient
map, including an arbitrary positive iterate.
-/

@[expose] public section

namespace Pcf

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- A finite prime-to-`p` map restricts to an actual finite return on
every invariant integral point closure, with prime-to-`p` monodromy. -/
theorem finiteType_pointClosureReturnMap_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsNormalScheme X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) (hx : f x = x) :
    IsPrimeToPMonodromyMap p (pointClosureReturnMap f x hx) := by
  have h := finiteType_pointClosureMap_primeToPMonodromy p hp k f s hmono x
  have hgeneral (y : X) (hxy : f x = y) :
      let g := pointClosureSubschemeMap f x y hxy
      letI : IsFinite g := pointClosureSubschemeMap_isFinite f x y hxy
      letI : IsDominant g := pointClosureSubschemeMap_isDominant f x y hxy
      IsPrimeToPMonodromyMap p g := by
    cases hxy
    exact h
  exact hgeneral x hx

/-- The canonical finite normalization lift of the return map on every
invariant integral point closure has prime-to-`p` monodromy. -/
theorem finiteType_pointClosureReturn_normalization_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsNormalScheme X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) (hx : f x = x) :
    let A := (pointClosureIdealSheaf x).subscheme
    letI : IsFinite (Palomar.normalizationMap A) := by
      letI : LocallyOfFiniteType ((pointClosureIdealSheaf x).subschemeι ≫ s) :=
        inferInstance
      exact schemeGlobalNormalizationMap_isFinite A k
        ((pointClosureIdealSheaf x).subschemeι ≫ s)
    letI : IsFinite (pointClosureReturnMap f x hx) :=
      pointClosureReturnMap_isFinite f x hx
    letI : IsDominant (pointClosureReturnMap f x hx) :=
      pointClosureReturnMap_isDominant f x hx
    IsPrimeToPMonodromyMap p
      (schemeGlobalNormalizationLift (pointClosureReturnMap f x hx)) := by
  let A := (pointClosureIdealSheaf x).subscheme
  let t : A ⟶ Spec (.of k) := (pointClosureIdealSheaf x).subschemeι ≫ s
  letI : LocallyOfFiniteType t := by infer_instance
  letI : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite A k t
  exact isPrimeToPMonodromyMap_schemeGlobalNormalizationLift p
    (pointClosureReturnMap f x hx)
    (finiteType_pointClosureReturnMap_primeToPMonodromy p hp k f s hmono x hx)

/-- The normalized return of any positive ambient iterate on a periodic
point closure has prime-to-`p` monodromy. -/
theorem finiteType_pointClosureReturn_iterate_normalization_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsNormalScheme X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (m : ℕ) (hm : 0 < m) (x : X)
    (hx : schemePointIterate f m x = x) :
    let g := (End.of f ^ m).asHom
    letI : IsFinite g := isFinite_end_pow f m
    letI : IsDominant g := isDominant_end_pow f m
    let A := (pointClosureIdealSheaf x).subscheme
    letI : IsFinite (Palomar.normalizationMap A) := by
      letI : LocallyOfFiniteType ((pointClosureIdealSheaf x).subschemeι ≫ s) :=
        inferInstance
      exact schemeGlobalNormalizationMap_isFinite A k
        ((pointClosureIdealSheaf x).subschemeι ≫ s)
    letI : IsFinite (pointClosureReturnMap g x hx) :=
      pointClosureReturnMap_isFinite g x hx
    letI : IsDominant (pointClosureReturnMap g x hx) :=
      pointClosureReturnMap_isDominant g x hx
    IsPrimeToPMonodromyMap p
      (schemeGlobalNormalizationLift
        (pointClosureReturnMap g x hx)) := by
  let g := (End.of f ^ m).asHom
  letI : IsFinite g := isFinite_end_pow f m
  letI : IsDominant g := isDominant_end_pow f m
  have hmono' : IsPrimeToPMonodromyMap p g :=
    isPrimeToPMonodromyMap_pow_pos p f hmono m hm
  exact finiteType_pointClosureReturn_normalization_primeToPMonodromy
    p hp k g s hmono' x hx

/-- The canonical normalized return of the periodic image of any eventually
periodic integral point closure has prime-to-`p` monodromy. -/
theorem finiteType_eventuallyPeriodicPointReturn_normalization_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsNormalScheme X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (r m : ℕ) (hm : 0 < m) (x : X)
    (hx : schemePointIterate f (r + m) x = schemePointIterate f r x) :
    let B := schemePointIterate f r x
    let A := (pointClosureIdealSheaf B).subscheme
    letI : IsFinite (Palomar.normalizationMap A) := by
      letI : LocallyOfFiniteType ((pointClosureIdealSheaf B).subschemeι ≫ s) :=
        inferInstance
      exact schemeGlobalNormalizationMap_isFinite A k
        ((pointClosureIdealSheaf B).subschemeι ≫ s)
    let g := eventuallyPeriodicPointReturn f r m x hx
    letI : IsFinite g := eventuallyPeriodicPointReturn_isFinite f r m x hx
    letI : IsDominant g := eventuallyPeriodicPointReturn_isDominant f r m x hx
    IsPrimeToPMonodromyMap p (schemeGlobalNormalizationLift g) := by
  exact finiteType_pointClosureReturn_iterate_normalization_primeToPMonodromy
    p hp k f s hmono m hm (schemePointIterate f r x)
      (schemePointIterate_periodic f r m x hx)

#print axioms finiteType_pointClosureReturnMap_primeToPMonodromy
#print axioms finiteType_pointClosureReturn_normalization_primeToPMonodromy
#print axioms finiteType_pointClosureReturn_iterate_normalization_primeToPMonodromy
#print axioms finiteType_eventuallyPeriodicPointReturn_normalization_primeToPMonodromy

end Pcf
