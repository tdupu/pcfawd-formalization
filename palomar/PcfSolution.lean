/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PcfAllTheWayDownCharZero

/-!
# Solution: PCF all the way down in characteristic zero

The proof half of the Palomar entry. Importing the development supplies, under the same
names, every declaration restated in `PcfChallenge`: the definitions with their actual
values, and proofs of `Pcf.pcfAllTheWayDown_charZero` and of every hole listed in
`comparator.json` (the supporting lemmas and the auxiliary `_proof_<n>` obligations of the
definitions). The main proof is `Pcf.pcfAllTheWayDown_charZero` in
`Pcf/Bounding/PcfAllTheWayDownCharZero.lean`. It depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/
