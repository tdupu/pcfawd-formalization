/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.FiniteSingularCorrection
import Pcf.Bounding.InvariantDivisorStep0Assembly

/-!
# The invariant-divisor theorem over a characteristic-zero field

The finite regularity correction is constructed from generic Cartier generation
and generic smoothness. Thus the only remaining mathematical inputs to the
invariant-divisor theorem are the local purity and Abhyankar packages.  The
local-domain consequence of regularity is derived from the proved Stacks Tag 00NP.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

variable (k : Type u) [Field k] [CharZero k]
  {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
  (f : X ⟶ X) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
  (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)

/-- The actual invariant-divisor setup with its finite regularity correction
constructed from the standing finite-type normal geometry. -/
def invariantDivisorSetupOfFiniteType
    (cover : ∀ (m : ℕ) (U : X.affineOpens)
        (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
        (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
          (finitePreimageAffine (End.of f ^ m) U : X.Opens)),
      InvariantDivisorLocalCoveringInputs f A m U Q' hx) :
    InvariantDivisorSchemeNormalizationPcfSetup X f A hA (SchemeDivisorPoint X)
      (SchemeDivisorPoint (schemeGlobalNormalization
        (pointClosureIdealSheaf A.1).subscheme)) :=
  invariantDivisorSetupOfFiniteRegularityCorrection k s f A hA
    (invariantDivisorSing A) (invariantDivisorSing_finite_of_perfectField k s A)
    (invariantDivisorSing_regular A) cover

/-- PCF on the canonical normalization of an actual invariant-divisor
restriction. Beyond the standing geometry and ambient PCF, the only inputs are
the local purity and Abhyankar packages bundled in `cover`; Tag 00NP is proved
separately. -/
theorem invariantDivisorNormalization_norm_pcf_of_finiteType
    (cover : ∀ (m : ℕ) (U : X.affineOpens)
        (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
        (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
          (finitePreimageAffine (End.of f ^ m) U : X.Opens)),
      InvariantDivisorLocalCoveringInputs f A m U Q' hx)
    (hpcf : letI := schemeStalkCharZeroOfField k s (genericPoint X)
      (divDynOfFiniteDominantNormalCharZero f).PCF) :
    (invariantDivisorNormalization k s f A hA).norm.PCF :=
  (invariantDivisorSetupOfFiniteType k s f A hA cover).norm_pcf hpcf

#print axioms invariantDivisorSetupOfFiniteType
#print axioms invariantDivisorNormalization_norm_pcf_of_finiteType
#check @invariantDivisorNormalization_norm_pcf_of_finiteType

end

end Pcf
