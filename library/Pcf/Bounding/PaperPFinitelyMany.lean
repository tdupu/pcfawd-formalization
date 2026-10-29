/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBadFiniteTopology
public import Pcf.Bounding.SchemeExtraction

/-!
# Integral effective divisors in a proper closed subset

This is the exact scheme-divisor formulation of `paper-p.tex`, Lemma
`lem:finitely-many`. The earlier general topological finiteness theorem
is applied to the codimension-one generic points of the divisors.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

namespace Pcf
universe u

/-- `paper-p.tex`, Lemma `lem:finitely-many`: a proper closed subset of an
integral Noetherian variety contains only finitely many integral effective
divisors, represented by their canonical reduced point-closures.

`paper-p.tex` correspondence: Lemma 7.3 (`lem:finitely-many`). -/
theorem finite_schemeDivisorPoint_closure_subset_of_proper_closed
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (Z : Set X) (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    {P : SchemeDivisorPoint X |
      closure ({P.1} : Set X) ⊆ Z}.Finite := by
  have hη : genericPoint X ∉ Z := by
    intro h
    have hcl : closure ({genericPoint X} : Set X) ⊆ Z :=
      closure_minimal (Set.singleton_subset_iff.mpr h) hZ
    rw [isGenericPoint_def.mp (genericPoint_spec X)] at hcl
    exact hproper (Set.univ_subset_iff.mp hcl)
  have hfinite := finite_coheight_one_of_isClosed Z hZ hη
  have himage : ((Subtype.val : SchemeDivisorPoint X → X) ''
      {P : SchemeDivisorPoint X | P.1 ∈ Z}).Finite := by
    apply hfinite.subset
    rintro x ⟨P, hP, rfl⟩
    exact ⟨hP, P.2⟩
  have hpoints : {P : SchemeDivisorPoint X | P.1 ∈ Z}.Finite :=
    himage.of_finite_image Subtype.val_injective.injOn
  apply hpoints.subset
  intro P hP
  exact hP (subset_closure (Set.mem_singleton P.1))

#print axioms finite_schemeDivisorPoint_closure_subset_of_proper_closed

end Pcf
