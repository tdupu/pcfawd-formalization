/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Palomar.Unconditional

/-!
# Solution: PCF all the way down in characteristic zero

The declarations compared with `PcfChallenge` are defined and proved in the `Pcf` development:
the statement surface in `Pcf.Palomar.Statement`; the non-vacuity theorems
`Pcf.Palomar.existsUnique_isNormalizationLift` and `Pcf.Palomar.exists_pointClosure_restriction`
in `Pcf.Palomar.Bridge`; and `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional` in
`Pcf.Palomar.Unconditional`, where it is derived from `Pcf.pcfAllTheWayDown_charZero` through
proved equivalences of every hypothesis and of the conclusion, with Zariski–Nagata purity
(`Pcf.Stacks.zariskiNagataPurity`, Stacks Tag 0BMB) and Abhyankar's lemma
(`Pcf.Stacks.abhyankarLemma`, Stacks Tags 0EYG/0EYH) supplied as proved theorems.
-/
