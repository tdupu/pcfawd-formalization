/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingMonodromy
public import Pcf.Examples.PaperP.FrobeniusPinchingBranchExact

/-!
# `ex:frobenius-pinching`: the sentence "Its function-field extension has Galois group
`(ℤ/2ℤ)²`, and its normalized branch divisors are the invariant axes, so `f` is PCF with
monodromy not divisible by `p`", as one statement

Source note: the manuscript states `p ≥ 5` but not `char k = p`; we assume `[CharP k p]`.
The Galois clause is stated for the generic stalk extension of the canonical lift
`H(x,y) = (x², y²)` on the normalization `A²`; the extension of `f` itself is isomorphic to it
(this transport is what `f_isPrimeToPMonodromyMap` uses).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingStatement

open AlgebraicGeometry
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators
open Pcf.Examples.PaperP.FrobeniusPinchingNormalization
open Pcf.Examples.PaperP.FrobeniusPinchingPCF
open Pcf.Examples.PaperP.FrobeniusPinchingGalois
open Pcf.Examples.PaperP.FrobeniusPinchingMonodromy
open Pcf.Examples.PaperP.FrobeniusPinchingBranchExact

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- `paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem frobeniusPinching_source_statement (hp : 5 ≤ p) :
    (letI := (Hs_generic_isField k).toField
     letI := ((Hs k).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.toAlgebra
     IsGalois ((Spec (.of (Plane k))).presheaf.stalk (Hs k (genericPoint (Spec (.of (Plane k))))))
        ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k))))) ∧
      Nonempty ((((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k))))) ≃ₐ[
        (Spec (.of (Plane k))).presheaf.stalk (Hs k (genericPoint (Spec (.of (Plane k)))))]
        ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k)))))) ≃*
          SignGroup)) ∧
    Pcf.weightedBranchPointSet (descendedSchemeMap k p) = Set.range (axisImage k p) ∧
    Function.Injective (axisImage k p) ∧
    (∀ i, descendedSchemeMap k p (axisImage k p i) = axisImage k p i) ∧
    Pcf.IsSeparableNormalizedPCF k (structureMap k p) (descendedSchemeMap k p) ∧
    Pcf.IsPaperPMonodromyNotDivisibleBy p (descendedSchemeMap k p) := by
  have h2 := two_ne_zero_of_charP k p (by omega)
  obtain ⟨hg, -, hG⟩ := Hs_generic_galois k h2 (Hs_generic_isField k)
  exact ⟨⟨hg, hG⟩, weightedBranchPointSet_eq k p h2, axisImage_injective k p, f_axisImage k p,
    (f_isPCF_with_monodromy_not_divisible k p hp).1,
    (f_isPCF_with_monodromy_not_divisible k p hp).2⟩

#print axioms frobeniusPinching_source_statement

end Pcf.Examples.PaperP.FrobeniusPinchingStatement
