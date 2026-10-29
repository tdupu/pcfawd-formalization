/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeFiniteResidueDelta
public import Pcf.Bounding.NonEtaleSeparableDynamics
public import Pcf.Bounding.SchemeWeightedCriticalFinite

/-!
# Weighted criticality and the non-étale divisor locus

For finite maps of normal varieties, the paper's weighted local degree
is the product of the ramification index and the residue-field
inseparable degree. This file begins the local comparison with the actual
non-étale stalk locus used by the recursive all-subvariety predicate.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

private theorem nat_mul_eq_one_iff_of_pos
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have hA : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have hB : b ≤ a * b := Nat.le_mul_of_pos_left b ha
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- At a divisor of a finite map, the local weight equals one precisely
when there is no ramification and the residue extension is separable. -/
theorem schemeDivisorDelta_eq_one_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (d : SchemeDivisorPoint X) :
    schemeDivisorDelta f d = 1 ↔
      schemeDivisorRamificationIdx f d = 1 ∧
        (letI := (f.residueFieldMap d.1).hom.toAlgebra
         Algebra.IsSeparable (Y.residueField (f d.1)) (X.residueField d.1)) := by
  letI := (f.residueFieldMap d.1).hom.toAlgebra
  letI : FiniteDimensional (Y.residueField (f d.1))
      (X.residueField d.1) := finiteResidueField_of_isFinite f d.1
  have he : 0 < schemeDivisorRamificationIdx f d :=
    schemeDivisorRamificationIdx_pos f d
  have hi : 0 < Field.finInsepDegree
      (Y.residueField (f d.1)) (X.residueField d.1) :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  change schemeDivisorRamificationIdx f d *
      Field.finInsepDegree (Y.residueField (f d.1)) (X.residueField d.1) = 1 ↔ _
  rw [nat_mul_eq_one_iff_of_pos he hi]
  exact and_congr Iff.rfl
    (isSeparable_iff_finInsepDegree_eq_one
      (Y.residueField (f d.1)) (X.residueField d.1)).symm

/-- Weighted criticality decomposes into ramification or residue-field
inseparability, for the actual finite map at an actual divisor. -/
theorem schemeDivisorDelta_one_lt_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (d : SchemeDivisorPoint X) :
    1 < schemeDivisorDelta f d ↔
      1 < schemeDivisorRamificationIdx f d ∨
        ¬(letI := (f.residueFieldMap d.1).hom.toAlgebra
          Algebra.IsSeparable (Y.residueField (f d.1)) (X.residueField d.1)) := by
  letI := (f.residueFieldMap d.1).hom.toAlgebra
  letI : FiniteDimensional (Y.residueField (f d.1))
      (X.residueField d.1) := finiteResidueField_of_isFinite f d.1
  have he : 0 < schemeDivisorRamificationIdx f d :=
    schemeDivisorRamificationIdx_pos f d
  have hi : 0 < Field.finInsepDegree
      (Y.residueField (f d.1)) (X.residueField d.1) :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  have hδ : 0 < schemeDivisorDelta f d :=
    schemeDivisorDelta_pos_of_isFinite f d
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have he1 : schemeDivisorRamificationIdx f d = 1 := by omega
    have hsep : Algebra.IsSeparable
        (Y.residueField (f d.1)) (X.residueField d.1) := hn.2
    have hδ1 := (schemeDivisorDelta_eq_one_iff f d).2 ⟨he1, hsep⟩
    omega
  · rintro (h | h)
    · by_contra hn
      have hδ1 : schemeDivisorDelta f d = 1 := by omega
      have he1 := (schemeDivisorDelta_eq_one_iff f d).1 hδ1 |>.1
      omega
    · by_contra hn
      have hδ1 : schemeDivisorDelta f d = 1 := by omega
      exact h ((schemeDivisorDelta_eq_one_iff f d).1 hδ1).2

#print axioms schemeDivisorDelta_eq_one_iff
#print axioms schemeDivisorDelta_one_lt_iff

end Pcf
