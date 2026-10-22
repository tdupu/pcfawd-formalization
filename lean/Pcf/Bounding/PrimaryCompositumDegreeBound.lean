/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryInseparableDegreeStep

/-!
# Degree bound after passing to a compositum

The induction in Stacks Project, Tag 04KM requires that forming a
compositum does not increase the degree remaining over the altered base.
The result below gives that inequality for literal intermediate fields in
one finite ambient extension. Combined with the preceding strict-drop
lemma, it is the numerical part of the alteration induction.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

/-- If two intermediate fields generate the full finite extension, the
degree over either one is at most the degree of the other over the
original base. -/
theorem finrank_le_of_intermediateField_sup_eq_top
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (A B : IntermediateField k L) (hAB : A ⊔ B = ⊤) :
    Module.finrank B L ≤ Module.finrank k A := by
  have hsup := IntermediateField.finrank_sup_le A B
  rw [hAB, IntermediateField.finrank_top'] at hsup
  have htower : Module.finrank k B * Module.finrank B L =
      Module.finrank k L := Module.finrank_mul_finrank k B L
  have hpos : 0 < Module.finrank k B := Module.finrank_pos
  nlinarith

#print axioms finrank_le_of_intermediateField_sup_eq_top

end Pcf.Bounding.PrimaryFibres
