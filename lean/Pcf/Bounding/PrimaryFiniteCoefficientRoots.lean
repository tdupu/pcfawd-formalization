/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFinitePureStage
public import Mathlib.FieldTheory.IsPerfectClosure

/-!
# Finite purely inseparable extensions containing coefficient roots

The field step in Stacks Project, Tag 04KM (used by `paper-p.tex`, Lemma
`lem:primary-fibres`) adjoins `p`th roots of finitely many coefficients.
Any perfect purely inseparable ambient field supplies the roots; the
finite-stage lemma confines them to one finite purely inseparable extension.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

/-- A finite collection of coefficients acquires `p`th roots in a finite
purely inseparable extension. This is the finite coefficient-root step of
Stacks Project, Tag 04KM, inside a perfect ambient extension. -/
theorem exists_finite_pure_extension_with_pth_roots
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsPurelyInseparable K E]
    (p : ℕ) [Fact p.Prime] [CharP E p] [PerfectRing E p]
    (s : Finset K) :
    ∃ F : IntermediateField K E,
      FiniteDimensional K F ∧ IsPurelyInseparable K F ∧
        ∀ a ∈ s, ∃ b : F, b ^ p = algebraMap K F a := by
  classical
  let root (a : K) : E :=
    (frobeniusEquiv E p).symm (algebraMap K E a)
  have hroot (a : K) : root a ^ p = algebraMap K E a := by
    exact (frobeniusEquiv E p).apply_symm_apply _
  obtain ⟨F, hfin, hpure, hs⟩ :=
    finite_set_contained_in_finite_pure_subextension K E
      (s.image root)
  refine ⟨F, hfin, hpure, ?_⟩
  intro a ha
  have hra : root a ∈ F := hs (root a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  refine ⟨⟨root a, hra⟩, ?_⟩
  apply Subtype.ext
  exact hroot a

#print axioms exists_finite_pure_extension_with_pth_roots

end Pcf.Bounding.PrimaryFibres
