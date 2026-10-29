/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PrimeToPConjugateFamily
public import Pcf.Bounding.SchemePrimeToPMonodromy
public import Pcf.Bounding.SchemeIteration

/-!
# Prime-to-characteristic monodromy under actual scheme iterates

The generic-stalk extension of a composite finite dominant morphism is the
tower of the two actual stalk maps. The field-theoretic normal-closure
composition lemma therefore applies to the scheme-level monodromy condition.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

set_option linter.style.haveILetI false

/-- The monodromy condition of `g` at a point known to be its source
generic point. The equality carries the field structures on both stalks. -/
private def monodromyAtGenericPoint
    (p : ℕ) {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsFinite g] [IsDominant g] [IsIntegral Y] [IsIntegral Z]
    (y : Y) (hy : y = genericPoint Y) : Prop := by
  have hgy : g y = genericPoint Z := by
    rw [hy]
    exact map_genericPoint_eq_of_isDominant g
  have hZ : IsField (Z.presheaf.stalk (g y)) :=
    hgy.symm ▸ Field.toIsField (Z.presheaf.stalk (genericPoint Z))
  have hY : IsField (Y.presheaf.stalk y) :=
    hy.symm ▸ Field.toIsField (Y.presheaf.stalk (genericPoint Y))
  letI : Field (Z.presheaf.stalk (g y)) := hZ.toField
  letI : Field (Y.presheaf.stalk y) := hY.toField
  letI : Algebra (Z.presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
    (g.stalkMap y).hom.toAlgebra
  exact IsPrimeToPMonodromy.{u, u, u} p
    (Z.presheaf.stalk (g y)) (Y.presheaf.stalk y)

private theorem monodromyAtGenericPoint_of_map
    (p : ℕ) {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsFinite g] [IsDominant g] [IsIntegral Y] [IsIntegral Z]
    (hg : IsPrimeToPMonodromyMap p g)
    (y : Y) (hy : y = genericPoint Y) :
    monodromyAtGenericPoint p g y hy := by
  subst y
  exact hg

/-- Prime-to-`p` monodromy of finite dominant maps is preserved by
composition. The three fields and their algebras are those of the actual
generic stalk maps, not abstract copies of a function field.

`paper-p.tex` correspondence: Lemma 6.2 (`lem:prime-to-p-compose`). -/
theorem isPrimeToPMonodromyMap_comp
    (p : ℕ) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] [IsDominant f] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (hf : IsPrimeToPMonodromyMap p f)
    (hg : IsPrimeToPMonodromyMap p g) :
    IsPrimeToPMonodromyMap p (f ≫ g) := by
  let x := genericPoint X
  have hfg : f x = genericPoint Y := map_genericPoint_eq_of_isDominant f
  have hgg : g (genericPoint Y) = genericPoint Z :=
    map_genericPoint_eq_of_isDominant g
  have hcomp : g (f x) = genericPoint Z := by
    rw [hfg]
    exact hgg
  let R := Z.presheaf.stalk (g (f x))
  let S := Y.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  have hRIsField : IsField (Z.presheaf.stalk (g (f x))) :=
    hcomp.symm ▸ Field.toIsField (Z.presheaf.stalk (genericPoint Z))
  have hSIsField : IsField (Y.presheaf.stalk (f x)) :=
    hfg.symm ▸ Field.toIsField (Y.presheaf.stalk (genericPoint Y))
  letI : Field R := hRIsField.toField
  letI : Field S := hSIsField.toField
  letI : Algebra R S := (g.stalkMap (f x)).hom.toAlgebra
  letI : Algebra S T := (f.stalkMap x).hom.toAlgebra
  letI : Algebra R T := ((f ≫ g).stalkMap x).hom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by
    change ((f ≫ g).stalkMap x).hom =
      (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom
    rw [Scheme.Hom.stalkMap_comp]
    rfl)
  have hf' : IsPrimeToPMonodromy.{u, u, u} p S T := by
    exact hf
  have hg' : IsPrimeToPMonodromy.{u, u, u} p R S := by
    exact monodromyAtGenericPoint_of_map p g hg (f x) hfg
  exact isPrimeToPMonodromy_tower p R S T hg' hf'

/-- Prime-to-`p` monodromy is preserved by every positive actual
categorical iterate of a finite dominant integral scheme endomorphism. -/
theorem isPrimeToPMonodromyMap_pow_succ
    (p : ℕ) {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X]
    (hmono : IsPrimeToPMonodromyMap p f) (m : ℕ) :
    IsPrimeToPMonodromyMap p (CategoryTheory.End.of f ^ (m + 1)).asHom := by
  induction m with
  | zero =>
      simpa only [zero_add, pow_one] using hmono
  | succ m ih =>
      have hcomp := isPrimeToPMonodromyMap_comp p f
        (CategoryTheory.End.of f ^ (m + 1)).asHom hmono ih
      simpa only [pow_succ, CategoryTheory.End.mul_asHom] using hcomp

/-- Paper `paper-p.tex`, Lemma `lem:prime-to-p-compose`: every positive
iterate of an actual finite dominant scheme self-map retains prime-to-`p`
monodromy.

`paper-p.tex` correspondence: Lemma 6.2 (`lem:prime-to-p-compose`). -/
theorem isPrimeToPMonodromyMap_pow_pos
    (p : ℕ) {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X]
    (hmono : IsPrimeToPMonodromyMap p f) (m : ℕ) (hm : 0 < m) :
    IsPrimeToPMonodromyMap p (CategoryTheory.End.of f ^ m).asHom := by
  cases m with
  | zero => cases hm
  | succ n =>
      simpa only [Nat.succ_eq_add_one] using
        isPrimeToPMonodromyMap_pow_succ p f hmono n

#print axioms isPrimeToPMonodromyMap_comp
#print axioms isPrimeToPMonodromyMap_pow_succ
#print axioms isPrimeToPMonodromyMap_pow_pos

end Pcf
