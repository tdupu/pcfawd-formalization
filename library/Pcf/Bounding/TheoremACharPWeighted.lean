/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremACharP
public import Pcf.Bounding.NormalDeltaNonEtalePCF

/-!
# Theorem A from the paper's weighted PCF hypothesis

The positive-characteristic statement in `latex/paper-p.tex`, Theorem
`thm:A`, uses the normalized critical locus defined by the weighted
local degree `δ`. The main recursive proof is phrased using non-étale
divisor stalks on the normalization. The two agree for separable maps
of normal schemes. Prime-to-`p` monodromy supplies separability, so the
paper's PCF and monodromy hypotheses suffice directly.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The paper's weighted normalized PCF predicate equals separable
normalized non-étale PCF when generic separability is recorded. -/
theorem isSeparableNormalizedPCF_iff_weightedNormalLift
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsSeparableNormalizedPCF k s f ↔
      (letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k s
       ∃ hsep : IsGenericallySeparable f,
         (schemeDeltaDynamicsOfFiniteDominantNormal
           (schemeGlobalNormalizationLift f)).IsPCF) := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  rw [isSeparableNormalizedPCF_iff_normalLift]
  constructor
  · rintro ⟨hsep, hpcf⟩
    exact ⟨hsep, (isNormalNonEtalePCF_iff_deltaPCF
      (schemeGlobalNormalizationLift f)
      (isGenericallySeparable_schemeGlobalNormalizationLift f hsep)).mp hpcf⟩
  · rintro ⟨hsep, hpcf⟩
    exact ⟨hsep, (isNormalNonEtalePCF_iff_deltaPCF
      (schemeGlobalNormalizationLift f)
      (isGenericallySeparable_schemeGlobalNormalizationLift f hsep)).mpr hpcf⟩

/-- **Theorem A in characteristic `p`, source-facing form.** The PCF
hypothesis is the paper's weighted normalized critical-locus PCF. The
prime-to-`p` monodromy hypothesis supplies generic separability, and the
conclusion is the recursive all-subvariety assertion on original reduced
returns in every codimension. -/
theorem isPCFAllSubvarieties_charP_of_weightedPCF
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf :
      letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k s
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).IsPCF)
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPCFAllSubvarieties k s f := by
  have hsep : IsGenericallySeparable f :=
    isGenericallySeparable_of_isPrimeToPMonodromyMap p f hmono
  have hpcf' : IsSeparableNormalizedPCF k s f :=
    (isSeparableNormalizedPCF_iff_weightedNormalLift k s f).mpr ⟨hsep, hpcf⟩
  exact isPCFAllSubvarieties_charP p hp k s f hpcf' hmono

#print axioms isSeparableNormalizedPCF_iff_weightedNormalLift
#print axioms isPCFAllSubvarieties_charP_of_weightedPCF

end
end Pcf
