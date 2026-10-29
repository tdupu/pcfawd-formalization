/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SeparablyGeneratedDescent

/-!
# The finite purely inseparable alteration `K'/K` in `lem:primary-fibres`

`paper-p.tex`, proof of Lemma `lem:primary-fibres`:

> Put `K = k(B)` and `L = k(E)`. Choose a finite purely inseparable `K'/K` such that the
> reduction of the generic fibre after base change is geometrically reduced (Stacks `04KT`).
> Its function field `L' = LK'` is geometrically reduced over `K'`. Write `[K':K] = p^a`.

Encoding. Everything sits inside an algebraically closed field `Ω ⊇ K`; the function field `L`
is `K(X)` for a finite set `X ⊆ Ω`. The alteration is `K' = K(T)` for a finite set `T` of
elements purely inseparable over `K`, and `L' = K'(X)` is the compositum `LK'`.

Divergence. The paper asks for `L'` geometrically reduced over `K'`. We prove the (stronger,
for finitely generated extensions equivalent) property that `L'` is *formally smooth* over
`K'`; this is what the remainder of the argument uses (it gives smoothness of the altered
morphism at the generic point). The route is the scoped Stacks `04KM` lemma
`Pcf.exists_finset_perfectClosure_formallySmooth_adjoin`, not Stacks `04KT` itself, so no
`04KT` tag is attached.
-/

@[expose] public section

namespace Pcf.Bounding.PaperPPrimaryFibres

open IntermediateField

universe u

/-- **The alteration `K'/K`.** For finitely many elements `X` of an algebraically closed
`Ω ⊇ K` there is a finite set `T ⊆ Ω` with `K' = K(T)` finite and purely inseparable over `K`
and `L' = K'(X)` formally smooth over `K'`. -/
theorem exists_finite_purelyInseparable_formallySmooth_adjoin (K Ω : Type u) [Field K]
    [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (X : Finset Ω) :
    ∃ T : Finset Ω, (T : Set Ω) ⊆ perfectClosure K Ω ∧
      FiniteDimensional K (adjoin K (T : Set Ω)) ∧
      IsPurelyInseparable K (adjoin K (T : Set Ω)) ∧
      Algebra.FormallySmooth (adjoin K (T : Set Ω))
        (adjoin (adjoin K (T : Set Ω)) (X : Set Ω)) := by
  obtain ⟨T, hT, hsm⟩ := Pcf.exists_finset_perfectClosure_formallySmooth_adjoin K Ω X
  have hle : adjoin K (T : Set Ω) ≤ perfectClosure K Ω := adjoin_le_iff.mpr hT
  have hpi : IsPurelyInseparable K (adjoin K (T : Set Ω)) :=
    (le_perfectClosure_iff K Ω _).mp hle
  refine ⟨T, hT, ?_, hpi, hsm⟩
  refine finiteDimensional_adjoin fun x hx => ?_
  have : IsIntegral K (⟨x, subset_adjoin K _ hx⟩ : adjoin K (T : Set Ω)) :=
    IsPurelyInseparable.isIntegral' K _
  exact this.map (adjoin K (T : Set Ω)).val

end Pcf.Bounding.PaperPPrimaryFibres

#print axioms Pcf.Bounding.PaperPPrimaryFibres.exists_finite_purelyInseparable_formallySmooth_adjoin
