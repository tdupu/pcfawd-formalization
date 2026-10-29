/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryCompositumDegreeBound
public import Mathlib.FieldTheory.LinearDisjoint

/-!
# Strict degree drop from a new common element of a compositum

In the induction of Stacks Project, Tag 04KM, an inseparable generator
of the old extension becomes separable after a finite pure alteration.
It then lies in both factors of the new compositum. This nontrivial
intersection forces a strict degree inequality.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

/-- In a finite compositum, a common element outside the original base
forces the degree over the second factor to be strictly smaller than the
degree of the first factor over the base. -/
theorem finrank_lt_of_intermediateField_sup_eq_top_of_common_element
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (A B : IntermediateField k L) (hAB : A ⊔ B = ⊤)
    (β : L) (hA : β ∈ A) (hB : β ∈ B)
    (hβ : β ∉ (⊥ : IntermediateField k L)) :
    Module.finrank B L < Module.finrank k A := by
  have hle := finrank_le_of_intermediateField_sup_eq_top k L A B hAB
  apply lt_of_le_of_ne hle
  intro heq
  have hsup : Module.finrank k (↥(A ⊔ B)) =
      Module.finrank k A * Module.finrank k B := by
    calc
      Module.finrank k (↥(A ⊔ B)) = Module.finrank k L := by
        rw [hAB, IntermediateField.finrank_top']
      _ = Module.finrank k B * Module.finrank B L :=
        (Module.finrank_mul_finrank k B L).symm
      _ = Module.finrank k A * Module.finrank k B := by
        rw [heq, mul_comm]
  have hdisjoint : A.LinearDisjoint B :=
    IntermediateField.LinearDisjoint.of_finrank_sup hsup
  have hinter : A ⊓ B = ⊥ := hdisjoint.inf_eq_bot
  exact hβ (hinter ▸ show β ∈ A ⊓ B from ⟨hA, hB⟩)

#print axioms finrank_lt_of_intermediateField_sup_eq_top_of_common_element

end Pcf.Bounding.PrimaryFibres
