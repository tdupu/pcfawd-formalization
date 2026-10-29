/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeLociCompare
public import Pcf.Bounding.SchemeWiring

/-!
# Orbits of branch divisors on the original scheme

This is the actual-scheme form of `paper-p.tex`, Corollary
`cor:orbit-unnormalized`.  It uses stalk non-étaleness and original-scheme
divisor pushforward, without passing to normalization.  The finite-support
corollary is the dynamical last step of Proposition `prop:normal-unnormalized`:
the missing geometric input is a uniform finite bound on the branch divisors
of all positive iterates of the restricted return map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf
universe u
noncomputable section
set_option linter.style.haveILetI false

/-- Corollary `cor:orbit-unnormalized`, case `i = 0`, for the original
scheme. Non-unramifiedness of the first stalk map persists through the tower,
so every forward image is a nonreduced-fiber branch divisor of an iterate.

`paper-p.tex` correspondence: Corollary A.7 (`cor:orbit-unnormalized`). -/
theorem schemeOrbitUnnormalizedZero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (g : X ⟶ X) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsLocallyNoetherian X]
    (n : ℕ) (Q : SchemeDivisorPoint X)
    (hQ : Q ∈ schemeUnnormalizedCriticalZero g) :
    schemeDivisorIterateOfFiniteType k s g n
        (schemeDivisorIterateOfFiniteType k s g 1 Q) ∈
        schemeUnnormalizedBranchZero (End.of g ^ (n + 1)).asHom := by
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField k s U
  have hQ₁ : Q ∈ schemeDivisorNonUnramifiedLocus (End.of g ^ 1).asHom := by
    simpa using hQ
  have h := schemeDivisorNonUnramifiedLocus_tower g n hQ₁
  apply (mem_schemeUnnormalizedBranchZero_iff_critical_divisor
    (End.of g ^ (n + 1)).asHom k _).2
  refine ⟨Q, ?_, h⟩
  simp only [schemeDivisorIterateOfFiniteType_val, pow_succ]
  rfl

/-- Corollary `cor:orbit-unnormalized`, case `i = 1`, for an actual finite
endomorphism on an original (possibly nonnormal) variety.

`paper-p.tex` correspondence: Corollary A.7 (`cor:orbit-unnormalized`). -/
theorem schemeOrbitUnnormalizedOne
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (g : X ⟶ X) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsLocallyNoetherian X]
    (n : ℕ) (Q : SchemeDivisorPoint X)
    (hQ : Q ∈ schemeUnnormalizedCriticalOne g) :
    schemeDivisorIterateOfFiniteType k s g n
        (schemeDivisorIterateOfFiniteType k s g 1 Q) ∈
        schemeUnnormalizedBranchOne (End.of g ^ (n + 1)).asHom ∨
    schemeDivisorIterateOfFiniteType k s g n
        (schemeDivisorIterateOfFiniteType k s g 1 Q) ∈
        schemeUnnormalizedBranchOne (End.of g ^ n).asHom := by
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField k s U
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField_finiteType k s U
  have hc := coheight_apply_eq_one_of_finiteType g k
  have hQ₁ : Q ∈ schemeDivisorNonEtaleLocus (End.of g ^ 1).asHom := by
    simpa using hQ
  rcases schemeDivisorNonEtaleLocus_tower g hc n Q hQ₁ with h | h
  · left
    refine ⟨Q.1, ?_, h⟩
    simp only [schemeDivisorIterateOfFiniteType_val, pow_succ]
    rfl
  · right
    refine ⟨g Q.1, ?_, h⟩
    simp only [schemeDivisorIterateOfFiniteType_val, pow_one]

/-- A uniform finite support for the branch divisors of all positive
iterates gives `1`-PCF on the original scheme. This is precisely the
dynamical step after `thm:bounding` in `prop:normal-unnormalized`. -/
theorem isSchemeUnnormalizedPCF_one_of_uniform_iterate_branch_support
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (g : X ⟶ X) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsLocallyNoetherian X]
    (Sig : Set (SchemeDivisorPoint X)) (hfinite : Sig.Finite)
    (hbound : ∀ m : ℕ, 1 ≤ m →
      schemeUnnormalizedBranchOne (End.of g ^ m).asHom ⊆ Sig) :
    IsSchemeUnnormalizedPCF true k s g := by
  apply hfinite.subset
  intro E hE
  simp only [schemeUnnormalizedPostcriticalSet, schemeUnnormalizedBranch,
    ite_true, Set.mem_iUnion, Set.mem_image] at hE
  obtain ⟨n, B, hB, rfl⟩ := hE
  obtain ⟨Q, hBQ, hQ⟩ :=
    (mem_schemeUnnormalizedBranchOne_iff_critical_divisor g B).mp hB
  have hB_eq : B = schemeDivisorIterateOfFiniteType k s g 1 Q := by
    apply Subtype.ext
    simpa only [schemeDivisorIterateOfFiniteType_val, pow_one] using hBQ.symm
  subst B
  rcases schemeOrbitUnnormalizedOne k s g n Q hQ with h | h
  · exact hbound (n + 1) (by omega) h
  · cases n with
    | zero =>
        have hzero : schemeDivisorIterateOfFiniteType k s g 0
            (schemeDivisorIterateOfFiniteType k s g 1 Q) =
            schemeDivisorIterateOfFiniteType k s g 1 Q := by
          apply Subtype.ext
          simp only [schemeDivisorIterateOfFiniteType_val, pow_zero]
          rfl
        rw [hzero]
        exact hbound 1 le_rfl (by simpa using hB)
    | succ n => exact hbound (n + 1) (by omega) h

/-- Both manuscript predicates follow from the same uniform branch bound:
the `0`-PCF conclusion uses `PC₀ ⊆ PC₁`. -/
theorem isSchemeUnnormalizedPCF_zero_one_of_uniform_iterate_branch_support
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (g : X ⟶ X) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsLocallyNoetherian X]
    (Sig : Set (SchemeDivisorPoint X)) (hfinite : Sig.Finite)
    (hbound : ∀ m : ℕ, 1 ≤ m →
      schemeUnnormalizedBranchOne (End.of g ^ m).asHom ⊆ Sig) :
    IsSchemeUnnormalizedPCF true k s g ∧
      IsSchemeUnnormalizedPCF false k s g := by
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField k s U
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField_finiteType k s U
  have h := isSchemeUnnormalizedPCF_one_of_uniform_iterate_branch_support
    k s g Sig hfinite hbound
  exact ⟨h, h.one_implies_zero k s g⟩

/-- Proposition `prop:normal-unnormalized`, with its remaining geometric
uniform-branch bound stated explicitly. The map is the return on the
original reduced subvariety `f^r(A)`, even when that subvariety is nonnormal.
The ambient PCF hypothesis and normality are needed to construct the bound;
they are not used by the dynamical implication proved here. -/
theorem preperiodicDivisor_isSchemeUnnormalizedPCF_of_uniform_iterate_branch_support
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    (A : SchemeDivisorPoint X) (r p : ℕ)
    (hA : (End.of f ^ (r + p)).asHom.base A.1 =
      (End.of f ^ r).asHom.base A.1) :
    let B := schemeDivisorIterateOfFiniteType k s f r A
    let sB := (pointClosureIdealSheaf B.1).subschemeι ≫ s
    let g := B.invariantClosureMap (End.of f ^ p).asHom
      (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)
    ∀ (Sig : Set (SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme)),
      Sig.Finite →
      (∀ m : ℕ, 1 ≤ m →
        schemeUnnormalizedBranchOne (End.of g ^ m).asHom ⊆ Sig) →
      IsSchemeUnnormalizedPCF true k sB g ∧
        IsSchemeUnnormalizedPCF false k sB g := by
  dsimp only
  intro Sig hfinite hbound
  exact isSchemeUnnormalizedPCF_zero_one_of_uniform_iterate_branch_support
    k _ _ Sig hfinite hbound

#print axioms schemeOrbitUnnormalizedOne
#print axioms schemeOrbitUnnormalizedZero
#print axioms isSchemeUnnormalizedPCF_one_of_uniform_iterate_branch_support
#print axioms isSchemeUnnormalizedPCF_zero_one_of_uniform_iterate_branch_support
#print axioms preperiodicDivisor_isSchemeUnnormalizedPCF_of_uniform_iterate_branch_support

end
end Pcf
