/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPPrimeToPTameFiniteMap
public import Pcf.Bounding.AllCentrePointClosureMonodromy
public import Pcf.Bounding.PaperPTower.RestrictionMonodromy

/-!
# Divisorial specialization in `paper-p.tex`

The ramification-index and residual monodromy conclusions of
`lem:prime-to-p-restrict` are packaged for the same actual divisor and
finite normal cover. The restricted map is on original reduced divisor
closures; no normality of those closures is assumed.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- `paper-p.tex`, `lem:prime-to-p-restrict`, in positive characteristic.
The second conjunct includes separability and prime-to-`p` degree of the
Galois closure of the residue-field extension.

`paper-p.tex` correspondence: Lemma 6.1 (`lem:prime-to-p-restrict`). -/
theorem paperP_primeToP_divisorialSpecialization
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f) (Q : SchemeDivisorPoint X) :
    ¬ p ∣ schemeDivisorRamificationIdx f Q ∧
      (let g := pointClosureSubschemeMap f Q.1 (f Q.1) rfl
       letI : IsFinite g := pointClosureSubschemeMap_isFinite f Q.1 (f Q.1) rfl
       letI : IsDominant g := pointClosureSubschemeMap_isDominant f Q.1 (f Q.1) rfl
       IsPrimeToPMonodromyMap p g) := by
  constructor
  · exact (finiteMap_schemeDivisor_tame_of_primeToP p hp k s f hmono Q).1
  · exact finiteType_pointClosureMap_primeToPMonodromy p hp k f s hmono Q.1

/-- The characteristic-zero case of `lem:prime-to-p-restrict`. The
ramification index is positive, hence not divisible by zero, and the
restricted finite map is generically separable. Every finite separable
extension in characteristic zero has finite Galois closure, for which
the order condition at `p = 0` is automatic.

`paper-p.tex` correspondence: Lemma 6.1 (`lem:prime-to-p-restrict`). -/
theorem paperP_primeToP_divisorialSpecialization_charZero
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (Q : SchemeDivisorPoint X) :
    ¬ 0 ∣ schemeDivisorRamificationIdx f Q ∧
      (let g := pointClosureSubschemeMap f Q.1 (f Q.1) rfl
       letI : IsFinite g := pointClosureSubschemeMap_isFinite f Q.1 (f Q.1) rfl
       letI : IsDominant g := pointClosureSubschemeMap_isDominant f Q.1 (f Q.1) rfl
       IsGenericallySeparableSchemeMap g) := by
  constructor
  · simpa using (schemeDivisorRamificationIdx_pos f Q).ne'
  · let g := pointClosureSubschemeMap f Q.1 (f Q.1) rfl
    letI : IsFinite g := pointClosureSubschemeMap_isFinite f Q.1 (f Q.1) rfl
    letI : IsDominant g := pointClosureSubschemeMap_isDominant f Q.1 (f Q.1) rfl
    exact PaperPTower.genericallySeparable_of_finite_charZero k
      ((pointClosureIdealSheaf (f Q.1)).subschemeι ≫ s) g

#print axioms paperP_primeToP_divisorialSpecialization
#print axioms paperP_primeToP_divisorialSpecialization_charZero

end Pcf
