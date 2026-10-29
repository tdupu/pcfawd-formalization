/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.WeightedBranchDictionary
public import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# The weighted local branch degree in a tower

The local multiplicity `δ=e f_insep` in `latex/paper-p.tex` is
multiplicative in a tower of finite maps. This is the numerical identity
used in the positive-characteristic cover descent and iterate arguments.
-/

@[expose] public section

namespace Pcf

universe u v w

set_option linter.style.haveILetI false

/-- Weighted multiplicity for a specified prime below `Q`. The explicit
prime avoids transporting dependent residue-field instances across an
equality of contracted ideals. -/
noncomputable def weightedLocalMultiplicity
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime]
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p] : ℕ :=
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  Q.ramificationIdx R * Field.finInsepDegree p.ResidueField Q.ResidueField

/-- The local weight with its canonical contracted prime is the
weighted branch multiplicity used by the paper's branch dictionary. -/
theorem weightedLocalMultiplicity_under
    (R : Type u) {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] :
    weightedLocalMultiplicity (Q.under R) Q =
      weightedDivisorMultiplicity R Q := rfl

/-- The actual ramification and residue-field factors of the weighted
local branch multiplicity obey the tower law. The flatness premise is
the one used by Mathlib's ramification-index tower theorem; it holds
for the divisor DVR extensions in the application. -/
theorem weightedLocalMultiplicity_tower
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Module.Flat S T]
    (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (Q : Ideal T) [Q.IsPrime] [Q.LiesOver P]
    (hAlg : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsAlgebraic p.ResidueField P.ResidueField) :
    letI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
    weightedLocalMultiplicity p Q =
      weightedLocalMultiplicity p P * weightedLocalMultiplicity P Q := by
  letI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI : Algebra.IsAlgebraic p.ResidueField P.ResidueField := hAlg
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  have hram := Ideal.ramificationIdx_tower (R := R) P Q
  have hres : Field.finInsepDegree p.ResidueField P.ResidueField *
      Field.finInsepDegree P.ResidueField Q.ResidueField =
      Field.finInsepDegree p.ResidueField Q.ResidueField :=
    Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic
      p.ResidueField P.ResidueField Q.ResidueField
  unfold weightedLocalMultiplicity
  rw [hram, ← hres]
  ac_rfl

#print axioms weightedLocalMultiplicity_under
#print axioms weightedLocalMultiplicity_tower

end Pcf
