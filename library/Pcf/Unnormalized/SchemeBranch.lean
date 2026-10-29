/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.DivisorLift
public import Pcf.Bounding.ReducedFiberBranch
public import Pcf.Bounding.CriticalLoci
public import Pcf.Bounding.CoverDescent

/-!
# The branch loci of an actual finite scheme map

This file gives the pointwise scheme meaning of the two unnormalized branch
loci in `paper-p.tex`, Definition `def:branch-loci`.  In particular, the
étale branch locus is defined using *all* points in the fiber, as in the
manuscript; the codimension-one restriction in Lemma `lem:branch-crit` is a
theorem, obtained from `coheight_eq_one_of_finite_preimage`.

The reduced-fiber branch locus is already defined in
`Pcf.Bounding.ReducedFiberBranch`.  The assertion equating it with the image
of the non-unramified critical locus on possibly nonnormal varieties is a
separate obligation.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

namespace Pcf

universe u

/-- Definition `def:branch-loci`(1): divisors with nonreduced scheme fiber.
The old name `schemeReducedFiberBranch` is retained as the implementation.

`paper-p.tex` correspondence: Definition A.1 (`def:branch-loci`). -/
abbrev schemeUnnormalizedBranchZero {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint Y) := schemeReducedFiberBranch g

/-- Definition `def:branch-loci`(2): divisors whose generic fiber contains a
point where the stalk map is not formally étale.  For a finite morphism of
varieties, formal étaleness here is equivalent to étaleness.

`paper-p.tex` correspondence: Definition A.1 (`def:branch-loci`). -/
def schemeUnnormalizedBranchOne {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint Y) :=
  {E | ∃ x : X, g x = E.1 ∧ SchemeStalkNotFormallyEtaleAt g x}

/-- Definition `def:crit-unnormalized`(1), with the actual stalk map.

`paper-p.tex` correspondence: Definition A.2 (`def:crit-unnormalized`). -/
abbrev schemeUnnormalizedCriticalZero {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint X) := schemeDivisorNonUnramifiedLocus g

/-- Definition `def:crit-unnormalized`(2), with the actual stalk map.

`paper-p.tex` correspondence: Definition A.2 (`def:crit-unnormalized`). -/
abbrev schemeUnnormalizedCriticalOne {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint X) := schemeDivisorNonEtaleLocus g

/-- Lemma `lem:branch-crit`, case `i = 1`: a point in the fiber over the
generic point of a target divisor is the generic point of a source divisor.
This remains true without characteristic-zero or normality assumptions. -/
theorem mem_schemeUnnormalizedBranchOne_iff_critical_divisor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] (E : SchemeDivisorPoint Y) :
    E ∈ schemeUnnormalizedBranchOne g ↔
      ∃ P : SchemeDivisorPoint X,
        g P.1 = E.1 ∧ P ∈ schemeUnnormalizedCriticalOne g := by
  constructor
  · rintro ⟨x, hx, hnot⟩
    let P : SchemeDivisorPoint X :=
      ⟨x, coheight_eq_one_of_finite_preimage g x (hx ▸ E.2)⟩
    exact ⟨P, hx, hnot⟩
  · rintro ⟨P, hP, hnot⟩
    exact ⟨P.1, hP, hnot⟩

/-- The set-level image formulation of Lemma `lem:branch-crit`, case `i = 1`,
using the existing finite-type divisor pushforward.

`paper-p.tex` correspondence: Lemma A.3 (`lem:branch-crit`). -/
theorem schemeUnnormalizedBranchOne_eq_image_critical
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y]
    (k : Type*) [Field k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)] :
    schemeUnnormalizedBranchOne g =
      (fun P : SchemeDivisorPoint X => P.mapFiniteDominantFiniteType g k) ''
        schemeUnnormalizedCriticalOne g := by
  ext E
  rw [mem_schemeUnnormalizedBranchOne_iff_critical_divisor]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨P, hP, hcrit⟩
    exact ⟨P, hcrit, Subtype.ext hP⟩
  · rintro ⟨P, hcrit, hP⟩
    exact ⟨P, congrArg Subtype.val hP, hcrit⟩

/-- Proposition `prop:loci-compare`(1), for the two unnormalized critical
loci.  The required generic formal étaleness follows from characteristic
zero for a finite dominant morphism of varieties; it is stated explicitly
here so the finiteness argument also applies in other characteristics. -/
theorem schemeUnnormalizedCritical_finite_of_generic_etale
    {X Y : Scheme.{u}} (g : X ⟶ Y) [LocallyOfFinitePresentation g]
    [IrreducibleSpace X] [NoetherianSpace X]
    (hgen : ∃ x : X, (g.stalkMap x).hom.FormallyEtale) :
    (schemeUnnormalizedCriticalZero g).Finite ∧
      (schemeUnnormalizedCriticalOne g).Finite := by
  have h₁ : (schemeDivisorNonEtaleLocus g).Finite :=
    schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale g hgen
  exact ⟨h₁.subset (schemeDivisorNonUnramifiedLocus_subset_nonEtaleLocus g), h₁⟩

/-- Proposition `prop:loci-compare`(1) in characteristic zero for an actual
finite dominant map.  Generic étaleness is supplied by the function-field
extension, not assumed as locus data.

`paper-p.tex` correspondence: Proposition A.4 (`prop:loci-compare`), item (1) of Proposition A.4
(`item:compare-finite`). -/
theorem schemeUnnormalizedCritical_finite_charZero
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [LocallyOfFinitePresentation g]
    [IsIntegral X] [IsIntegral Y] [NoetherianSpace X]
    [CharZero (Y.presheaf.stalk (genericPoint Y))] :
    (schemeUnnormalizedCriticalZero g).Finite ∧
      (schemeUnnormalizedCriticalOne g).Finite :=
  schemeUnnormalizedCritical_finite_of_generic_etale g
    ⟨genericPoint X, formallyEtale_stalkMap_genericPoint_of_cover_charZero g⟩

/-- The étale branch locus has finitely many divisorial components under
the hypotheses of the preceding critical-locus finiteness theorem. -/
theorem schemeUnnormalizedBranchOne_finite_of_generic_etale
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [LocallyOfFinitePresentation g]
    [IsIntegral X] [IsIntegral Y] [NoetherianSpace X]
    (k : Type*) [Field k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)]
    (hgen : ∃ x : X, (g.stalkMap x).hom.FormallyEtale) :
    (schemeUnnormalizedBranchOne g).Finite := by
  rw [schemeUnnormalizedBranchOne_eq_image_critical g k]
  exact ((schemeUnnormalizedCritical_finite_of_generic_etale g hgen).2).image _

/-- The `i = 1` branch-locus finiteness consequence of
Proposition `prop:loci-compare`(1) for characteristic-zero varieties. -/
theorem schemeUnnormalizedBranchOne_finite_charZero
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [LocallyOfFinitePresentation g]
    [IsIntegral X] [IsIntegral Y] [NoetherianSpace X]
    [CharZero (Y.presheaf.stalk (genericPoint Y))]
    (k : Type*) [Field k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)] :
    (schemeUnnormalizedBranchOne g).Finite := by
  rw [schemeUnnormalizedBranchOne_eq_image_critical g k]
  exact (schemeUnnormalizedCritical_finite_charZero g).2.image _

#print axioms mem_schemeUnnormalizedBranchOne_iff_critical_divisor
#print axioms schemeUnnormalizedBranchOne_eq_image_critical
#print axioms schemeUnnormalizedCritical_finite_of_generic_etale
#print axioms schemeUnnormalizedCritical_finite_charZero
#print axioms schemeUnnormalizedBranchOne_finite_of_generic_etale
#print axioms schemeUnnormalizedBranchOne_finite_charZero

end Pcf
