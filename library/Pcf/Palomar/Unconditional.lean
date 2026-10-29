/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Palomar.Bridge
public import Pcf.Stacks.Purity.Tag0BMA
public import Pcf.Stacks.Abhyankar.FiniteNormalization

/-!
# PCF all the way down in characteristic zero, unconditionally

The two local theorems that `Pcf.pcfAllTheWayDown_charZero` takes as inputs (the structure
`Pcf.PCFAllTheWayDownLocalTheorems`) are proved in this repository:

* Zariski--Nagata purity (Stacks `0BMB`, affine pointwise form):
  `Pcf.Stacks.zariskiNagataPurity : ∀ R S, Pcf.Stacks.ZariskiNagataPurity R S`
  (`Pcf/Stacks/Purity/Tag0BMA.lean`);
* Abhyankar's lemma for a regular divisor (Stacks `0EYG`/`0EYH`, all positive integers
  invertible): `Pcf.Stacks.abhyankarLemma : ∀ R S a, Pcf.Stacks.AbhyankarLemma R S a`
  (`Pcf/Stacks/Abhyankar/FiniteNormalization.lean`; the normalization is proved finite).

This file discharges those inputs:

* `Pcf.pcfAllTheWayDownLocalTheorems`: the structure `Pcf.PCFAllTheWayDownLocalTheorems`, built
  from the two theorems;
* `Pcf.pcfAllTheWayDown_charZero_unconditional`: the development-side statement with no inputs;
* `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional`: the same theorem in the compact
  vocabulary of `Pcf.Palomar.Statement`, transported along the equivalences of
  `Pcf.Palomar.Bridge`.  This is the theorem compared by the Palomar Challenge
  (`PcfChallenge.lean`, beside `Pcf.lean`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

/-- The two local literature theorems of `PCFAllTheWayDownLocalTheorems`, proved:
purity by `Pcf.Stacks.zariskiNagataPurity` (Stacks `0BMB`) and Abhyankar's lemma by
`Pcf.Stacks.abhyankarLemma` (Stacks `0EYG`/`0EYH`). -/
theorem pcfAllTheWayDownLocalTheorems : PCFAllTheWayDownLocalTheorems.{u} where
  purity R S _ _ _ := Stacks.zariskiNagataPurity R S
  abhyankar R S _ _ _ a := Stacks.abhyankarLemma R S a

/-- **PCF all the way down in characteristic zero** (`cor:pcfawd`), with no hypotheses beyond
those of the statement. This is `Pcf.pcfAllTheWayDown_charZero` applied to
`pcfAllTheWayDownLocalTheorems`, i.e. with Zariski--Nagata purity
(`Pcf.Stacks.zariskiNagataPurity`) and Abhyankar's lemma (`Pcf.Stacks.abhyankarLemma`)
discharged. -/
theorem pcfAllTheWayDown_charZero_unconditional
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : IsNormalizedPCFOfFiniteType k s f) :
    SchemePCFAllTheWayDown k s f :=
  pcfAllTheWayDown_charZero pcfAllTheWayDownLocalTheorems k s f hpcf

end Pcf

namespace Pcf.Palomar

/-- **PCF all the way down in characteristic zero**, unconditionally, in the compact vocabulary
of `Pcf.Palomar.Statement`.  This is `Pcf.pcfAllTheWayDown_charZero_unconditional` transported
along `isNormalizedPCF_iff_scheme` and `pcfAllTheWayDown_iff_scheme`. -/
theorem pcfAllTheWayDown_charZero_unconditional
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : IsNormalizedPCF f) :
    PCFAllTheWayDown f :=
  (pcfAllTheWayDown_iff_scheme k s f).mpr <|
    Pcf.pcfAllTheWayDown_charZero_unconditional k s f ((isNormalizedPCF_iff_scheme k s f).mp hpcf)

end Pcf.Palomar

#print axioms Pcf.pcfAllTheWayDownLocalTheorems
#print axioms Pcf.pcfAllTheWayDown_charZero_unconditional
#print axioms Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional
#check @Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional
#check @Pcf.pcfAllTheWayDown_charZero_unconditional
