/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AffineSchemeRamification
public import Pcf.Bounding.SchemeIteration
public import Pcf.Bounding.NormalizationPcfEquiv

/-!
# Actual geometric assembly for an invariant divisor

The affine branch-avoidance condition follows from the branch locus of the
actual ambient divisor dynamics. Codimension, source incidence, normalization,
and the two finite correction sets are supplied by the geometric constructions.
The covering inputs are exactly purity and the Abhyankar package on the local
chart rings.  The needed local-domain consequence of regularity is derived by
the proved Stacks Tag 00NP theorem.

The general constructor permits any finite exceptional set whose complement
has regular ambient and divisor stalks. Its singular-locus specialization takes
closedness of the two actual singular loci, in addition to the covering inputs.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

section AffineBranch

variable {X : Scheme.{u}} (f : X ⟶ X)
  [IsFinite f] [IsDominant f] [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormalScheme X] [NoetherianSpace X]
  [CharZero (X.presheaf.stalk (genericPoint X))]

local instance affineCorrectionAlgebra (U : X.affineOpens) :
    Algebra Γ(X, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra

attribute [local instance] IsLocallyNoetherian.component_noetherian

local instance affineCorrectionFinite (U : X.affineOpens) :
    Module.Finite Γ(X, U) Γ(X, finitePreimageAffine f U) :=
  moduleFinite_finitePreimageAffine f U

local instance affineCorrectionSourceNoetherian (U : X.affineOpens) :
    IsNoetherianRing Γ(X, finitePreimageAffine f U) :=
  IsNoetherianRing.of_finite Γ(X, U) Γ(X, finitePreimageAffine f U)

local instance affineCorrectionFaithful (U : X.affineOpens) :
    FaithfulSMul Γ(X, U) Γ(X, finitePreimageAffine f U) :=
  faithfulSMul_finitePreimageAffine f U

/-- Every branch divisor on a finite affine preimage chart is an actual branch
divisor of the scheme endomorphism. -/
theorem schemeDivisorPointOfAffinePrime_mem_branch
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (E : HeightOnePrime Γ(X, U))
    (hE : E ∈ heightOneBranch (R := Γ(X, U))
      (S := Γ(X, finitePreimageAffine f U))) :
    schemeDivisorPointOfAffinePrime U E ∈
      (divisorDynamicsOfFiniteDominantNormalCharZero f).branch := by
  obtain ⟨F, hF, rfl⟩ := hE
  refine ⟨schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) F, ?_, ?_⟩
  · exact Subtype.ext (schemeDivisorPointOfAffinePrime_map f U F)
  · change 1 < schemeDivisorRamificationIdx f
      (schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) F)
    rw [schemeDivisorRamificationIdx_eq_heightOneRamificationIdx f U F]
    exact hF

/-- Avoidance of actual ambient branch components implies the affine branch
avoidance condition used by the local bounding theorem. -/
theorem notMem_finiteAffineOtherBranchLocus_of_meets
    (A : SchemeDivisorPoint X)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (hQU : (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ (U : X.Opens))
    (hmeets : ∀ E ∈ (divisorDynamicsOfFiniteDominantNormalCharZero f).branch,
      E ≠ A → Q ∉ invariantDivisorMeets A E) :
    (⟨(pointClosureIdealSheaf A.1).subschemeι Q.1, hQU⟩ : (U : X.Opens)) ∉
      finiteAffineOtherBranchLocus (f := f) U
        (affinePrimeOfSchemeDivisorPoint A U
          (A.mem_affine_of_pointClosurePoint_mem U Q.1 hQU)) := by
  rintro ⟨E, hE, hEA, hinc⟩
  apply hmeets (schemeDivisorPointOfAffinePrime U E)
    (schemeDivisorPointOfAffinePrime_mem_branch f U E hE)
  · intro heq
    apply hEA
    apply schemeDivisorPointOfAffinePrime_injective U
    exact heq.trans (schemeDivisorPointOfAffinePrime_affinePrime A U _).symm
  · exact schemeDivisorPointOfAffinePrime_mem_closure U E _ hinc

end AffineBranch

section CoveringInputs

variable {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f]

attribute [local instance] invariantIterateFinitePreimageAlgebra

/-- The two classical local covering inputs, on precisely the rings extracted
from an ambient iterate and a source point of the reduced divisor. No divisor
restriction or étaleness conclusion is included in this bundle. -/
structure InvariantDivisorLocalCoveringHypotheses
    (A : SchemeDivisorPoint X) (m : ℕ) (U : X.affineOpens)
    (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)) : Prop where
  purity : Stacks.ZariskiNagataPurity
    (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 hx).under Γ(X, U)))
    (Localization (Algebra.algebraMapSubmonoid
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U)
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 hx).under
          Γ(X, U)).primeCompl))
  abhyankar : ∀ a : Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 hx).under Γ(X, U)),
    Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 hx).under Γ(X, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) Q'.1 hx).under
            Γ(X, U)).primeCompl)) a

end CoveringInputs

section Assembly

variable (k : Type u) [Field k] [CharZero k]
  {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
  (f : X ⟶ X) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
  (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)

/-- Assemble the literal local Step-0 datum using regularity of the two actual
stalks and avoidance of actual ambient branch components. In particular, source
incidence, ambient codimension two, and affine branch avoidance are proved. -/
def invariantDivisorCorrectionLocalDataOfRegular
    (m : ℕ) (Q Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hambient : (pointClosureIdealSheaf A.1).subschemeι Q.1 ∉ stalkSingularLocus X)
    (hdivisor : Q.1 ∉ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme)
    (hmeets : letI := charZero_stalk_of_field k s (genericPoint X)
      ∀ E ∈ (divisorDynamicsOfFiniteDominantNormalCharZero f).iterate m |>.branch,
        E ≠ A → Q ∉ invariantDivisorMeets A E)
    (hQQ : (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom.base Q'.1 = Q.1)
    (cover : ∀ (U : X.affineOpens) (hx : Q'.1 ∈
        (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)),
      InvariantDivisorLocalCoveringHypotheses f A m U Q' hx) :
    InvariantDivisorCorrectionLocalData X f A m Q Q' := by
  letI := charZero_stalk_of_field k s (genericPoint X)
  let hex := exists_isAffineOpen_mem_and_subset
    (show (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ (⊤ : X.Opens) by trivial)
  let U : X.affineOpens := ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  have hQU : (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ (U : X.Opens) :=
    (Classical.choose_spec hex).2.1
  have hx := A.invariantClosureIterate_source_mem f hA m U Q Q' hQU hQQ
  refine
    { U := U
      rationalAlgebra := schemeAffineRationalAlgebraOfField k s U
      target_mem := hQU
      source_mem := hx
      ambient_coheight := A.closureDivisor_coheight_of_finiteType k s Q
      ambient_regular := hambient
      divisor_regular := hdivisor
      branch_avoid := ?_
      purity := (cover U hx).purity
      abhyankar := (cover U hx).abhyankar }
  let : Nonempty (U : X.Opens) :=
    ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q.1, hQU⟩⟩
  let : Nonempty (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens) :=
    ⟨⟨(pointClosureIdealSheaf A.1).subschemeι Q'.1, hx⟩⟩
  apply notMem_finiteAffineOtherBranchLocus_of_meets
    (CategoryTheory.End.of f ^ m).asHom A Q U hQU
  intro E hE hEA
  rw [divisorDynamicsOfFiniteDominantNormalCharZero_pow_eq_iterate] at hE
  exact hmeets E hE hEA

/-- Actual invariant-divisor setup for any finite geometric correction set
whose complement has regular ambient and divisor stalks. This constructor is
reusable with a singular locus, a smooth-complement correction, or another
proved finite regularity correction. -/
def invariantDivisorSetupOfFiniteRegularityCorrection
    (sing : Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme))
    (hsing : sing.Finite)
    (hregular : ∀ Q, Q ∉ sing →
      (pointClosureIdealSheaf A.1).subschemeι Q.1 ∉ stalkSingularLocus X ∧
        Q.1 ∉ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme)
    (cover : ∀ (m : ℕ) (U : X.affineOpens)
        (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
        (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)),
      InvariantDivisorLocalCoveringHypotheses f A m U Q' hx) :
    InvariantDivisorSchemeNormalizationPCFSetup X f A hA (SchemeDivisorPoint X)
      (SchemeDivisorPoint (Palomar.normalization
        (pointClosureIdealSheaf A.1).subscheme)) := by
  letI := charZero_stalk_of_field k s (genericPoint X)
  exact InvariantDivisorSchemeNormalizationPCFSetup.ofActualAmbient f A hA
    (invariantDivisorNormalization k s f A hA)
    (invariantDivisorNormalization_g k s f A hA)
    sing hsing (invariantDivisorMeets A) (invariantDivisorMeets_finite A)
    (by
      intro m _ Q hQ hmeets Q' hQQ
      apply invariantDivisorCorrectionLocalDataOfRegular k s f A hA m Q Q'
        (hregular Q hQ).1 (hregular Q hQ).2 hmeets
      · exact (invariantDivisorNormalization_iterate_step_val k s f A hA m Q').symm.trans
          (congrArg Subtype.val hQQ)
      · exact fun U hx ↦ cover m U Q' hx)

/-- The invariant-divisor setup formed from the actual two singular loci.
Outside the standing finite-type normal geometry, the only inputs are their
closedness and the two classical covering theorems. -/
def invariantDivisorSetupOfClosedSingularLoci
    (hX : IsClosed (stalkSingularLocus X))
    (hSingA : IsClosed (stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme))
    (cover : ∀ (m : ℕ) (U : X.affineOpens)
        (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
        (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)),
      InvariantDivisorLocalCoveringHypotheses f A m U Q' hx) :
    InvariantDivisorSchemeNormalizationPCFSetup X f A hA (SchemeDivisorPoint X)
      (SchemeDivisorPoint (Palomar.normalization
        (pointClosureIdealSheaf A.1).subscheme)) :=
  invariantDivisorSetupOfFiniteRegularityCorrection k s f A hA
    (invariantDivisorSing A) (invariantDivisorSing_finite_of_isClosed A hX hSingA)
    (invariantDivisorSing_regular A) cover

/-- Postcritical finiteness on the canonical normalization of the actual
invariant-divisor restriction, with a proved finite regularity correction. -/
theorem invariantDivisorNormalization_normalized_isPCF_of_finiteRegularityCorrection
    (sing : Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme))
    (hsing : sing.Finite)
    (hregular : ∀ Q, Q ∉ sing →
      (pointClosureIdealSheaf A.1).subschemeι Q.1 ∉ stalkSingularLocus X ∧
        Q.1 ∉ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme)
    (cover : ∀ (m : ℕ) (U : X.affineOpens)
        (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
        (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)),
      InvariantDivisorLocalCoveringHypotheses f A m U Q' hx)
    (hpcf : letI := charZero_stalk_of_field k s (genericPoint X)
      (divisorDynamicsOfFiniteDominantNormalCharZero f).IsPCF) :
    (invariantDivisorNormalization k s f A hA).normalized.IsPCF :=
  (invariantDivisorSetupOfFiniteRegularityCorrection k s f A hA
    sing hsing hregular cover).normalized_isPCF hpcf

/-- The normal invariant-divisor theorem for actual scheme maps and canonical
normalization, conditional only on the two singular-locus closedness statements
and purity/Abhyankar beyond the standing geometric and PCF hypotheses. -/
theorem invariantDivisorNormalization_normalized_isPCF_of_closedSingularLoci
    (hX : IsClosed (stalkSingularLocus X))
    (hSingA : IsClosed (stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme))
    (cover : ∀ (m : ℕ) (U : X.affineOpens)
        (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
        (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)),
      InvariantDivisorLocalCoveringHypotheses f A m U Q' hx)
    (hpcf : letI := charZero_stalk_of_field k s (genericPoint X)
      (divisorDynamicsOfFiniteDominantNormalCharZero f).IsPCF) :
    (invariantDivisorNormalization k s f A hA).normalized.IsPCF :=
  (invariantDivisorSetupOfClosedSingularLoci k s f A hA hX hSingA cover).normalized_isPCF hpcf

end Assembly

#print axioms schemeDivisorPointOfAffinePrime_mem_branch
#print axioms notMem_finiteAffineOtherBranchLocus_of_meets
#print axioms invariantDivisorCorrectionLocalDataOfRegular
#print axioms invariantDivisorSetupOfFiniteRegularityCorrection
#print axioms invariantDivisorSetupOfClosedSingularLoci
#print axioms invariantDivisorNormalization_normalized_isPCF_of_finiteRegularityCorrection
#print axioms invariantDivisorNormalization_normalized_isPCF_of_closedSingularLoci
#check @InvariantDivisorLocalCoveringHypotheses
#check @invariantDivisorCorrectionLocalDataOfRegular
#check @invariantDivisorSetupOfClosedSingularLoci
#check @invariantDivisorNormalization_normalized_isPCF_of_closedSingularLoci

end

end Pcf
