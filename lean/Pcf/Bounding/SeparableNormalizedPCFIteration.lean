/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeWeightedIteration
public import Pcf.Bounding.AllSubvarietyIterationSeparable

/-!
# Iteration of normalized non-étale PCF

This transports the normal weighted iteration theorem through the actual
canonical global normalization lift. It supplies the root PCF portion of
`paper-p.tex`, Lemma `lem:allsubvar-iterate`, in arbitrary characteristic.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The characteristic-free separable normalized PCF predicate is normal
non-étale PCF of the actual finite normalization lift. -/
theorem isSeparableNormalizedPCF_iff_normalLift
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    IsSeparableNormalizedPCF k s f ↔
      (letI : IsFinite (Palomar.normalizationMap X) :=
         schemeGlobalNormalizationMap_isFinite X k s
      ∃ hsep : IsGenericallySeparable f,
        IsNormalNonEtalePCF (schemeGlobalNormalizationLift f)
          (isGenericallySeparable_schemeGlobalNormalizationLift f hsep)) := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  rfl

/-- Separable normalized non-étale PCF is invariant under every positive
iterate of a finite dominant endomorphism of an integral finite-type
scheme over an arbitrary field. -/
theorem isSeparableNormalizedPCF_pow_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (m : ℕ) (hm : 1 ≤ m) :
    IsSeparableNormalizedPCF k s (End.of f ^ m).asHom ↔
      IsSeparableNormalizedPCF k s f := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  rw [isSeparableNormalizedPCF_iff_normalLift k s (End.of f ^ m).asHom,
    isSeparableNormalizedPCF_iff_normalLift k s f]
  constructor
  · rintro ⟨hsepPow, hpcfPow⟩
    have hsep : IsGenericallySeparable f :=
      isGenericallySeparable_of_pow f m hm hsepPow
    refine ⟨hsep, ?_⟩
    have hpcfPow' : IsNormalNonEtalePCF
        (End.of (schemeGlobalNormalizationLift f) ^ m).asHom
        (isGenericallySeparable_pow (schemeGlobalNormalizationLift f)
          (isGenericallySeparable_schemeGlobalNormalizationLift f hsep) m) := by
      simpa only [← schemeGlobalNormalizationLift_pow] using hpcfPow
    exact (isNormalNonEtalePCF_pow_iff
      (schemeGlobalNormalizationLift f)
      (isGenericallySeparable_schemeGlobalNormalizationLift f hsep)
      m hm).mp hpcfPow'
  · rintro ⟨hsep, hpcf⟩
    have hsepPow : IsGenericallySeparable (End.of f ^ m).asHom :=
      isGenericallySeparable_pow f hsep m
    refine ⟨hsepPow, ?_⟩
    have hpcfPow := (isNormalNonEtalePCF_pow_iff
      (schemeGlobalNormalizationLift f)
      (isGenericallySeparable_schemeGlobalNormalizationLift f hsep)
      m hm).mpr hpcf
    simpa only [schemeGlobalNormalizationLift_pow] using hpcfPow

#print axioms isSeparableNormalizedPCF_iff_normalLift
#print axioms isSeparableNormalizedPCF_pow_iff

end Pcf
