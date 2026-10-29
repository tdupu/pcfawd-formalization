/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeBoundingCharZero
public import Pcf.Unnormalized.SchemeOrbit

/-!
# The original-scheme unnormalized PCF return

This assembles the fixed divisor correction in `paper-p.tex`, Proposition
`prop:normal-unnormalized`, with the actual return map on the original
reduced divisor. The key identification is that iterating this restriction
is the same morphism as restricting the ambient iterate.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section
set_option linter.style.haveILetI false

/-- The branch₁ divisors of every iterate of the original reduced divisor
return lie in the exact bounding correction for the ambient iterate. -/
theorem paperPBoundingCharZero_invariant_iterate_branchOne_subset_sigma
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint X) (hB : f B.1 = B.1) (m : ℕ) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
    let g := B.invariantClosureMap f hB
    schemeUnnormalizedBranchOne (End.of g ^ m).asHom ⊆
      {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
        Q.1 ∈ paperPBoundingSigma (End.of f ^ m).asHom B} := by
  let F : X ⟶ X := (End.of f ^ m).asHom
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  have hBm : F B.1 = B.1 := end_pow_apply_eq_of_apply_eq f B.1 hB m
  have hBmap : B.mapFiniteDominantNormal F = B := Subtype.ext hBm
  let P (C : SchemeDivisorPoint X) (hC : F B.1 = C.1) : Prop :=
    schemeUnnormalizedBranchOne (pointClosureSubschemeMap F B.1 C.1 hC) ⊆
      {Q : SchemeDivisorPoint (pointClosureIdealSheaf C.1).subscheme |
        Q.1 ∈ paperPBoundingSigma F C}
  have hsub : P (B.mapFiniteDominantNormal F) rfl :=
    paperPBoundingCharZero_branchOne_subset_sigma k s F B
  have hsub0 : ∀ hC : F B.1 = (B.mapFiniteDominantNormal F).1,
      P (B.mapFiniteDominantNormal F) hC := by
    intro hC
    exact hsub
  have hsubB : ∀ hC : F B.1 = B.1, P B hC :=
    Eq.ndrec (motive := fun C : SchemeDivisorPoint X =>
      ∀ hC : F B.1 = C.1, P C hC) hsub0 hBmap
  have hsub' := hsubB hBm
  change schemeUnnormalizedBranchOne
      (pointClosureSubschemeMap F B.1 B.1 hBm) ⊆
      {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
        Q.1 ∈ paperPBoundingSigma F B} at hsub'
  simpa only [F, ← B.invariantClosureMap_iterate f hB m] using hsub'

#print axioms paperPBoundingCharZero_invariant_iterate_branchOne_subset_sigma

/-- The original reduced invariant-divisor return has one finite set of
branch₁ divisors containing the branch loci of all positive iterates.
The set depends only on the ambient PCF map and the divisor.

`paper-p.tex` correspondence: Proposition A.14 (`prop:normal-unnormalized`). -/
theorem paperPBoundingCharZero_invariant_uniform_branchOne_support
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : (letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
      (weightedPostcriticalPointSet f).Finite))
    (B : SchemeDivisorPoint X) (hB : f B.1 = B.1) :
    let g := B.invariantClosureMap f hB
    ∃ Sig : Set (SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme),
      Sig.Finite ∧ ∀ m : ℕ, 1 ≤ m →
        schemeUnnormalizedBranchOne (End.of g ^ m).asHom ⊆ Sig := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  let I := pointClosureIdealSheaf B.1
  let W := closure {y : X | y ∈ weightedPostcriticalPointSet f ∧ y ≠ B.1}
  let Sig : Set (SchemeDivisorPoint I.subscheme) :=
    {Q | Q.1 ∈ (I.subschemeι ⁻¹' W ∪
      I.subschemeι ⁻¹' stalkSingularLocus X) ∪
        stalkSingularLocus I.subscheme}
  have hfinite : Sig.Finite :=
    paperPBoundingCharZero_fixedSigmaDivisors_finite k s f hpcf B
  refine ⟨Sig, hfinite, ?_⟩
  intro m hm Q hQ
  have hSigma :=
    paperPBoundingCharZero_invariant_iterate_branchOne_subset_sigma
      k s f B hB m hQ
  have hother := paperPBoundingCharZero_otherBranch_iterate_subset_fixed
    k s f B m
  change Q.1 ∈
    (I.subschemeι ⁻¹' paperPBoundingOtherBranch (End.of f ^ m).asHom B ∪
      I.subschemeι ⁻¹' stalkSingularLocus X) ∪
        stalkSingularLocus I.subscheme at hSigma
  change Q.1 ∈ (I.subschemeι ⁻¹' W ∪
    I.subschemeι ⁻¹' stalkSingularLocus X) ∪
      stalkSingularLocus I.subscheme
  rcases hSigma with (hOther | hAmbient) | hDivisor
  · exact Or.inl (Or.inl (hother hOther))
  · exact Or.inl (Or.inr hAmbient)
  · exact Or.inr hDivisor

#print axioms paperPBoundingCharZero_invariant_uniform_branchOne_support

/-- The original reduced return on an invariant integral effective divisor
of a normal characteristic-zero PCF variety is both `1`-PCF and `0`-PCF.
This is the invariant-divisor case of `prop:normal-unnormalized`. -/
theorem paperP_normalInvariantDivisor_isSchemeUnnormalizedPCF
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : (letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
      (weightedPostcriticalPointSet f).Finite))
    (B : SchemeDivisorPoint X) (hB : f B.1 = B.1) :
    let g := B.invariantClosureMap f hB
    let sB := (pointClosureIdealSheaf B.1).subschemeι ≫ s
    IsSchemeUnnormalizedPCF true k sB g ∧
      IsSchemeUnnormalizedPCF false k sB g := by
  obtain ⟨Sig, hfinite, hbound⟩ :=
    paperPBoundingCharZero_invariant_uniform_branchOne_support
      k s f hpcf B hB
  exact isSchemeUnnormalizedPCF_zero_one_of_uniform_iterate_branch_support
    k _ _ Sig hfinite hbound

#print axioms paperP_normalInvariantDivisor_isSchemeUnnormalizedPCF

/-- Proposition `prop:normal-unnormalized` for the actual original reduced
return of every eventually periodic integral effective divisor.

`paper-p.tex` correspondence: Proposition A.14 (`prop:normal-unnormalized`). -/
theorem paperP_normalPreperiodicDivisor_isSchemeUnnormalizedPCF
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : (letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
      (weightedPostcriticalPointSet f).Finite))
    (A : SchemeDivisorPoint X) (r p : ℕ) (hp : 1 ≤ p)
    (hA : (End.of f ^ (r + p)).asHom.base A.1 =
      (End.of f ^ r).asHom.base A.1) :
    let B := schemeDivisorIterateOfFiniteType k s f r A
    let sB := (pointClosureIdealSheaf B.1).subschemeι ≫ s
    let g := B.invariantClosureMap (End.of f ^ p).asHom
      (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)
    IsSchemeUnnormalizedPCF true k sB g ∧
      IsSchemeUnnormalizedPCF false k sB g := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  let F : X ⟶ X := (End.of f ^ p).asHom
  have hpcfF : (weightedPostcriticalPointSet F).Finite := by
    change (weightedPostcriticalPointSet (End.of f ^ p).asHom).Finite
    rw [weightedPostcriticalPointSet_pow_eq f p hp]
    exact hpcf
  exact paperP_normalInvariantDivisor_isSchemeUnnormalizedPCF k s F hpcfF
    (schemeDivisorIterateOfFiniteType k s f r A)
    (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)

#print axioms paperP_normalPreperiodicDivisor_isSchemeUnnormalizedPCF

/-- On a characteristic-zero variety, original-scheme `1`-PCF implies
weighted normalized PCF. This is the comparison used when a normal divisor
becomes the ambient variety at the next step of `cor:chains-unnormalized`. -/
theorem weightedPostcriticalPointSet_finite_of_schemeUnnormalizedPCF_one
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf1 : IsSchemeUnnormalizedPCF true k s f) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
    (weightedPostcriticalPointSet f).Finite := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  letI (U : X.affineOpens) : Algebra k Γ(X, U) :=
    schemeAffineAlgebraOfField k s U
  letI (U : X.affineOpens) : Algebra.FiniteType k Γ(X, U) :=
    schemeAffineAlgebraOfField_finiteType k s U
  have hpcf0 : IsSchemeUnnormalizedPCF false k s f :=
    hpcf1.one_implies_zero k s f
  have hpow (n : ℕ) (x : X) :
      (End.of f ^ n).asHom x = (f : X → X)^[n] x := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [pow_succ', End.mul_asHom, Scheme.Hom.comp_apply,
          Function.iterate_succ_apply', ih]
  apply (hpcf0.image (fun Q : SchemeDivisorPoint X => Q.1)).subset
  intro y hy
  obtain ⟨n, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
  obtain ⟨E, heq, hE⟩ :=
    weightedBranchPointSet_subset_schemeUnnormalizedBranchZero_points
      f k s s hz
  subst z
  refine ⟨schemeDivisorIterateOfFiniteType k s f n E, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨n, E, by simpa [schemeUnnormalizedBranch] using hE, rfl⟩
  · change (schemeDivisorIterateOfFiniteType k s f n E).1 = (f : X → X)^[n] E.1
    rw [schemeDivisorIterateOfFiniteType_val]
    exact hpow n E.1

#print axioms weightedPostcriticalPointSet_finite_of_schemeUnnormalizedPCF_one

/-- Corollary `cor:chains-unnormalized`, stated as the property of every
finite chain of original reduced integral effective divisor returns. At each
step the chosen divisor return is both `1`-PCF and `0`-PCF. A normality
witness is requested only when that divisor becomes the ambient variety
for another step; the final divisor may be nonnormal.

`paper-p.tex` correspondence: Corollary A.16 (`cor:chains-unnormalized`). -/
def IsSchemeUnnormalizedPCFAlongNormalDivisorChains
    (k : Type u) [Field k] [CharZero k]
    (n : ℕ) {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] : Prop :=
  match n with
  | 0 => True
  | n + 1 =>
      ∀ (A : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
        (hA : (End.of f ^ (r + p)).asHom.base A.1 =
          (End.of f ^ r).asHom.base A.1),
        let B := schemeDivisorIterateOfFiniteType k s f r A
        let D := (pointClosureIdealSheaf B.1).subscheme
        let sD := (pointClosureIdealSheaf B.1).subschemeι ≫ s
        let g := B.invariantClosureMap (End.of f ^ p).asHom
          (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)
        IsSchemeUnnormalizedPCF true k sD g ∧
          IsSchemeUnnormalizedPCF false k sD g ∧
          ∀ (hnormal : IsNormalScheme D),
            letI : IsNormalScheme D := hnormal
            IsSchemeUnnormalizedPCFAlongNormalDivisorChains k n sD g

/-- Every finite chain of periodic or eventually periodic integral effective
divisor returns through normal intermediate varieties has `1`-PCF and
`0`-PCF at each step, including a possibly nonnormal last divisor.

`paper-p.tex` correspondence: Corollary A.16 (`cor:chains-unnormalized`). -/
theorem paperP_normalDivisorChains_areSchemeUnnormalizedPCF
    (k : Type u) [Field k] [CharZero k]
    (n : ℕ) {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : (letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
      (weightedPostcriticalPointSet f).Finite)) :
    IsSchemeUnnormalizedPCFAlongNormalDivisorChains k n s f := by
  induction n generalizing X s f with
  | zero => trivial
  | succ n ih =>
      intro A r p hp hA
      let B := schemeDivisorIterateOfFiniteType k s f r A
      let D := (pointClosureIdealSheaf B.1).subscheme
      let sD := (pointClosureIdealSheaf B.1).subschemeι ≫ s
      let g := B.invariantClosureMap (End.of f ^ p).asHom
        (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)
      have hchild : IsSchemeUnnormalizedPCF true k sD g ∧
          IsSchemeUnnormalizedPCF false k sD g :=
        paperP_normalPreperiodicDivisor_isSchemeUnnormalizedPCF
          k s f hpcf A r p hp hA
      refine ⟨hchild.1, hchild.2, ?_⟩
      intro hnormal
      letI : IsNormalScheme D := hnormal
      have hweight : (letI : IsFinite (Palomar.normalizationMap D) :=
          schemeGlobalNormalizationMap_isFinite D k sD
          (weightedPostcriticalPointSet g).Finite) :=
        weightedPostcriticalPointSet_finite_of_schemeUnnormalizedPCF_one
          k sD g hchild.1
      exact ih sD g hweight

#print axioms IsSchemeUnnormalizedPCFAlongNormalDivisorChains
#print axioms paperP_normalDivisorChains_areSchemeUnnormalizedPCF

end
end Pcf
