/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Palomar.Bridge
public import Pcf.Stacks.Purity.Tag0BMA
public import Pcf.Stacks.Abhyankar.FiniteNormalization

/-!
# PCF all the way down in characteristic zero, unconditionally

The two local theorems that `Pcf.pcfAllTheWayDown_charZero` and
`Pcf.Palomar.pcfAllTheWayDown_charZero` take as inputs are now proved in this repository:

* Zariski--Nagata purity (Stacks `0BMB`, affine pointwise form):
  `Pcf.Stacks.zariskiNagataPurity : ∀ R S, Pcf.Stacks.ZariskiNagataPurity R S`, with Palomar form
  `Pcf.Palomar.zariskiNagataPurity` (`Pcf/Stacks/Purity/Tag0BMA.lean`);
* Abhyankar's lemma for a regular divisor (Stacks `0EYG`/`0EYH`, all positive integers
  invertible): `Pcf.Stacks.abhyankarLemma : ∀ R S a, Pcf.Stacks.AbhyankarLemma R S a`
  (`Pcf/Stacks/Abhyankar/FiniteNormalization.lean`; the normalization is proved finite), with
  Palomar form `Pcf.Palomar.abhyankarLemma` (`Pcf/Stacks/Abhyankar/Tag0EYG.lean`; the
  Palomar statement assumes the normalization finite).

This file discharges those inputs:

* `Pcf.pcfAllTheWayDownLocalTheorems`: the structure `Pcf.PCFAllTheWayDownLocalTheorems`, built
  from the two theorems;
* `Pcf.pcfAllTheWayDown_charZero_unconditional`: the development-side statement with no inputs;
* `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional`: the compared Palomar statement with the
  `purity` and `abhyankar` binders removed and nothing else changed.
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

/-- **PCF all the way down in characteristic zero**, unconditionally.

The statement is that of the compared theorem `Pcf.Palomar.pcfAllTheWayDown_charZero` with its
`purity` and `abhyankar` binders removed. Those two inputs are supplied by
`Pcf.Palomar.zariskiNagataPurity` (Zariski--Nagata purity, Stacks `0BMB`) and
`Pcf.Palomar.abhyankarLemma` (Abhyankar's lemma, Stacks `0EYG`/`0EYH`), both proved in
this repository. -/
theorem pcfAllTheWayDown_charZero_unconditional
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : IsNormalizedPCF f) :
    PCFAllTheWayDown f :=
  pcfAllTheWayDown_charZero (fun R S _ _ _ ↦ Pcf.Palomar.zariskiNagataPurity R S)
    (fun R S _ _ _ a ↦ Pcf.Palomar.abhyankarLemma R S a) k s f hpcf

end Pcf.Palomar

#print axioms Pcf.pcfAllTheWayDownLocalTheorems
#print axioms Pcf.pcfAllTheWayDown_charZero_unconditional
#print axioms Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional
#check @Pcf.Palomar.pcfAllTheWayDown_charZero
#check @Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional
#check @Pcf.pcfAllTheWayDown_charZero_unconditional
