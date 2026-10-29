/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeBranch
public import Pcf.Unnormalized.SchemeOrbit
public import Pcf.Bounding.PaperPBoundingCharZeroPointwise
public import Pcf.Bounding.PaperPIteration

/-!
# Bounding the branch divisors of the original reduced restriction

This is the branch-locus consequence of the pointwise characteristic-zero
bounding chart in `paper-p.tex`, Theorem `thm:bounding`.  The map below is the
actual finite map between original reduced divisor closures.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section
set_option linter.style.haveILetI false

/-- A branch divisor of the original reduced restriction must lie in the
manuscript's exact exceptional set `Σ`. -/
theorem paperPBoundingCharZero_branchOne_subset_sigma
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    let B := A.mapFiniteDominantNormal f
    schemeUnnormalizedBranchOne (A.closureMapFiniteDominantNormal f) ⊆
      {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
        Q.1 ∈ paperPBoundingSigma f B} := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  dsimp only
  intro Q hQ
  obtain ⟨x, hx, hnot⟩ := hQ
  by_contra hSigma
  exact hnot (paperPBoundingCharZero_at_formallyEtale k s f A x Q hx hSigma)

/-- In characteristic zero the exact exceptional set `Σ` contains only
finitely many integral effective divisor generic points. This conclusion
uses the finite correction proven in Step 0, without requiring closedness
of the full singular locus. -/
theorem paperPBoundingCharZero_sigmaDivisors_finite
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    let B := A.mapFiniteDominantNormal f
    {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
      Q.1 ∈ paperPBoundingSigma f B}.Finite := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  let B := A.mapFiniteDominantNormal f
  let I := pointClosureIdealSheaf B.1
  let Sigma : Set I.subscheme := I.subschemeι ⁻¹' paperPBoundingOtherBranch f B
  have hbad := paperPBoundingStepZero_badDivisors_finite_charZero k s f A
  change ({Q : SchemeDivisorPoint I.subscheme |
      closure ({Q.1} : Set I.subscheme) ⊆ Sigma} ∪
      invariantDivisorSing B).Finite at hbad
  apply hbad.subset
  intro Q hQ
  change Q.1 ∈ (Sigma ∪ I.subschemeι ⁻¹' stalkSingularLocus Y) ∪
    stalkSingularLocus I.subscheme at hQ
  rcases hQ with (hother | hamb) | hdiv
  · left
    exact closure_minimal (Set.singleton_subset_iff.mpr hother)
      (isClosed_closure.preimage I.subschemeι.continuous)
  · right
    left
    exact hamb
  · right
    right
    exact hdiv

/-- The actual finite map of original reduced divisors has a finite
unnormalized étale branch locus.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharZero_branchOne_finite
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X) :
    (schemeUnnormalizedBranchOne (A.closureMapFiniteDominantNormal f)).Finite := by
  exact (paperPBoundingCharZero_sigmaDivisors_finite k s f A).subset
    (paperPBoundingCharZero_branchOne_subset_sigma k s f A)

/-- Ambient PCF bounds all non-`B` weighted branch components of every
iterate inside a single closed set, the union of all other postcritical
components of the original map. -/
theorem paperPBoundingCharZero_otherBranch_iterate_subset_fixed
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint X) (m : ℕ) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
    paperPBoundingOtherBranch (End.of f ^ m).asHom B ⊆
      closure {y : X | y ∈ weightedPostcriticalPointSet f ∧ y ≠ B.1} := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  dsimp only [paperPBoundingOtherBranch]
  apply closure_mono
  intro y hy
  exact ⟨weightedBranchPointSet_pow_subset_postcritical f m hy.1, hy.2⟩

/-- The fixed exceptional set from the manuscript proof contains only
finitely many divisor generic points of `B`, even though the actual
singular loci need not yet be known to be closed. -/
theorem paperPBoundingCharZero_fixedSigmaDivisors_finite
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : (letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
      (weightedPostcriticalPointSet f).Finite))
    (B : SchemeDivisorPoint X) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k s
    let W := closure {y : X | y ∈ weightedPostcriticalPointSet f ∧ y ≠ B.1}
    let I := pointClosureIdealSheaf B.1
    {Q : SchemeDivisorPoint I.subscheme |
      Q.1 ∈ (I.subschemeι ⁻¹' W ∪
        I.subschemeι ⁻¹' stalkSingularLocus X) ∪
        stalkSingularLocus I.subscheme}.Finite := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  let S : Set X := {y | y ∈ weightedPostcriticalPointSet f ∧ y ≠ B.1}
  let W := closure S
  let I := pointClosureIdealSheaf B.1
  have hS : S.Finite := hpcf.subset (fun y hy => hy.1)
  have hcodim : ∀ y ∈ S, Order.coheight y = 1 := by
    intro y hy
    obtain ⟨n, z, hz, rfl⟩ := Set.mem_iUnion.mp hy.1
    have hiter : ∀ n : ℕ, Order.coheight ((f : X → X)^[n] z) = 1 := by
      intro n
      induction n with
      | zero => exact weightedBranchPointSet_coheight_one k s f hz
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          exact coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k s f ⟨_, ih⟩
    exact hiter n
  have hB : B.1 ∉ W :=
    schemeDivisorPoint_notMem_closure_other_finite_divisors B S hS hcodim
      (fun h => h.2 rfl)
  have hW : IsClosed (I.subschemeι ⁻¹' W) :=
    isClosed_closure.preimage I.subschemeι.continuous
  have hproper : I.subschemeι ⁻¹' W ≠ Set.univ := by
    intro h
    have hg : genericPoint I.subscheme ∈ I.subschemeι ⁻¹' W :=
      h.symm ▸ Set.mem_univ _
    change I.subschemeι (genericPoint I.subscheme) ∈ W at hg
    rw [pointClosureSubscheme_genericPoint] at hg
    exact hB hg
  have hother : {Q : SchemeDivisorPoint I.subscheme |
      Q.1 ∈ I.subschemeι ⁻¹' W}.Finite :=
    finite_schemeDivisorPoint_mem_of_isClosed hW hproper
  have hsing : (invariantDivisorSing B).Finite :=
    invariantDivisorSing_finite_of_perfectField k s B
  apply (hother.union hsing).subset
  intro Q hQ
  rcases hQ with (hWQ | hXQ) | hIQ
  · exact Or.inl hWQ
  · exact Or.inr (Or.inl hXQ)
  · exact Or.inr (Or.inr hIQ)

#print axioms paperPBoundingCharZero_branchOne_subset_sigma
#print axioms paperPBoundingCharZero_sigmaDivisors_finite
#print axioms paperPBoundingCharZero_branchOne_finite
#print axioms paperPBoundingCharZero_otherBranch_iterate_subset_fixed
#print axioms paperPBoundingCharZero_fixedSigmaDivisors_finite

end
end Pcf
