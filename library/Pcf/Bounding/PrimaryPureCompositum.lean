/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryPureTensorReduction
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The finite purely inseparable compositum in the primary-fibres lemma

For a field extension `E/K` and a purely inseparable extension `P/K`,
the reduction of `E ⊗[K] P` is the compositum field. It is purely
inseparable over `E`, and finite when `P/K` is finite. This supplies the
field `L' = LK'` in `paper-p.tex`, Lemma `lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

set_option linter.style.haveILetI false

open Algebra
open scoped TensorProduct

universe u

variable (K E P : Type u) [Field K] [Field E] [Field P]
  [Algebra K E] [Algebra K P] [IsPurelyInseparable K P]

/-- The reduced tensor product carrying the compositum of `E` and `P`. -/
abbrev pureCompositum :=
  (E ⊗[K] P) ⧸ nilradical (E ⊗[K] P)

/-- The reduced tensor product is a field, not a product of field factors. -/
@[instance_reducible]
noncomputable def pureCompositumField : Field (pureCompositum K E P) :=
  (purelyInseparable_reduced_tensor_isField K P E).toField

/-- The compositum field is purely inseparable over the original field. -/
theorem pureCompositum_isPurelyInseparable :
    IsPurelyInseparable E (pureCompositum K E P) := by
  haveI : IsDomain (pureCompositum K E P) :=
    (purelyInseparable_reduced_tensor_isField K P E).isDomain
  let q := ringExpChar K
  let _ : ExpChar E q :=
    expChar_of_injective_algebraMap (algebraMap K E).injective q
  apply (isPurelyInseparable_iff_pow_mem E q).2
  intro x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ :=
    IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
      (k := K) (K := P) q t
  obtain ⟨a, ha⟩ := hn
  refine ⟨n, ⟨a, ?_⟩⟩
  change algebraMap E (pureCompositum K E P) a =
    (Ideal.Quotient.mk (nilradical (E ⊗[K] P)) t) ^ q ^ n
  rw [← map_pow (Ideal.Quotient.mk (nilradical (E ⊗[K] P))) t (q ^ n)]
  rw [← ha]
  rfl

omit [IsPurelyInseparable K P] in
/-- If the purely inseparable base alteration is finite, so is its
compositum with any field extension. -/
theorem pureCompositum_finite [FiniteDimensional K P] :
    FiniteDimensional E (pureCompositum K E P) := by
  haveI : Module.Finite E (E ⊗[K] P) := inferInstance
  infer_instance

/-- The generic degree of the finite purely inseparable compositum is
a power of the characteristic. -/
theorem pureCompositum_finrank_eq_pow [FiniteDimensional K P]
    (p : ℕ) [ExpChar E p] :
    letI : Field (pureCompositum K E P) := pureCompositumField K E P
    ∃ a : ℕ, Module.finrank E (pureCompositum K E P) = p ^ a := by
  letI : Field (pureCompositum K E P) := pureCompositumField K E P
  haveI : FiniteDimensional E (pureCompositum K E P) :=
    pureCompositum_finite K E P
  haveI : IsPurelyInseparable E (pureCompositum K E P) :=
    pureCompositum_isPurelyInseparable K E P
  exact IsPurelyInseparable.finrank_eq_pow E (pureCompositum K E P) p

#print axioms pureCompositum_isPurelyInseparable
#print axioms pureCompositum_finite
#print axioms pureCompositum_finrank_eq_pow

end Pcf.Bounding.PrimaryFibres
