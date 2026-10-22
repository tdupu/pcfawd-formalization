/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Embeddings of the separable closure

Let `E / K` be finite and `F` a `K`-algebra isomorphic to the separable
closure of `K` in `E`. Any `K`-embedding `F ⟶ E` has image the separable
closure, so `E` is purely inseparable over `F`. This is the field step that
makes the factor `ρ` purely inseparable in `latex/paper-p.tex`, Lemma
`lem:pcf-transfer-charp`.
-/

@[expose] public section

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- An embedding of a copy of the separable closure makes the top field
purely inseparable over it. -/
theorem isPurelyInseparable_of_algHom_separableClosure
    (K E F : Type*) [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
    [FiniteDimensional K E]
    (ψ : F →ₐ[K] E) (e : F ≃ₐ[K] separableClosure K E) :
    letI : Algebra F E := ψ.toRingHom.toAlgebra
    IsPurelyInseparable F E := by
  letI : Algebra F E := ψ.toRingHom.toAlgebra
  let R : IntermediateField K E := ψ.fieldRange
  let eR : F ≃ₐ[K] R := AlgEquiv.ofInjectiveField ψ
  haveI : Algebra.IsSeparable K R :=
    Algebra.IsSeparable.of_algHom K (separableClosure K E) (eR.symm.trans e).toAlgHom
  have hle : R ≤ separableClosure K E := le_separableClosure K E R
  have hfin : Module.finrank K R = Module.finrank K (separableClosure K E) :=
    eR.symm.toLinearEquiv.finrank_eq.trans e.toLinearEquiv.finrank_eq
  have heq : R = separableClosure K E := IntermediateField.eq_of_le_of_finrank_eq hle hfin
  let q := ringExpChar K
  haveI : ExpChar F q := expChar_of_injective_ringHom (algebraMap K F).injective q
  haveI : ExpChar (separableClosure K E) q :=
    expChar_of_injective_ringHom (algebraMap K (separableClosure K E)).injective q
  rw [isPurelyInseparable_iff_pow_mem F q]
  intro x
  obtain ⟨n, y, hy⟩ :=
    (isPurelyInseparable_iff_pow_mem (separableClosure K E) q).mp inferInstance x
  refine ⟨n, ?_⟩
  have hmem : x ^ q ^ n ∈ R := by
    rw [heq, ← hy]
    exact y.2
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

#print axioms isPurelyInseparable_of_algHom_separableClosure

end
end Pcf
