/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalNonnormal
public import Pcf.Bounding.TheoremAWeightedDownstairs
public import Pcf.Bounding.PaperPDictionary
public import Pcf.Bounding.AllSubvarietyRecursive

/-!
# `f` is PCF in the sense of `def:pcf` (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): "`f` is PCF". The manuscript's
`def:pcf` is encoded as `Pcf.IsSeparableNormalizedPCF k s f`: `f` is generically separable and the
weighted (`δ`) branch dynamics of its normalization lift is post-critically finite.

* `deltaDynamics_isPCF_of_etale` (general): an étale finite dominant endomorphism of a normal
  locally Noetherian integral scheme has `δ = 1` on every divisor
  (`paperP_divisorDelta_eq_one_iff_etaleAt`), so there are no critical divisors and the
  post-critical set is empty;
* `X_isLocallyNoetherian`, `X_isNoetherian`;
* `fX_isGenericallySeparable` (from prime-to-3 monodromy);
* `normalizationLift_etale`: the normalization lift of `f` is `F̃`, which is étale;
* **`fX_isSeparableNormalizedPCF : Pcf.IsSeparableNormalizedPCF k sX f`**.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

universe u

set_option linter.style.haveILetI false

/-- **An étale finite dominant endomorphism has PCF `δ`-dynamics** (no divisor has `δ > 1`). -/
theorem deltaDynamics_isPCF_of_etale {N : Scheme.{u}} (g : N ⟶ N) [IsFinite g] [IsDominant g]
    [IsIntegral N] [IsLocallyNoetherian N] [Pcf.IsNormalScheme N] [Etale g] :
    (Pcf.schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF := by
  have hcrit : (Pcf.schemeDeltaDynamicsOfFiniteDominantNormal g).critical = ∅ := by
    ext d
    simp only [Pcf.DeltaDynamics.critical, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      Pcf.schemeDeltaDynamics_delta]
    have h1 : Pcf.schemeDivisorDelta g d = 1 := by
      rw [Pcf.paperP_divisorDelta_eq_one_iff_etaleAt]
      obtain ⟨U, hU, hgU, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show g d.1 ∈ (⊤ : N.Opens) from trivial)
      obtain ⟨V, hV, hdV, hVle⟩ :=
        exists_isAffineOpen_mem_and_subset (show d.1 ∈ g ⁻¹ᵁ U from hgU)
      exact ⟨U, hU, V, hV, hVle, hdV,
        HasRingHomProperty.appLE (P := @Etale) g ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVle⟩
    rw [h1]
    exact lt_irrefl 1
  have hpost : (Pcf.schemeDeltaDynamicsOfFiniteDominantNormal g).postcriticalSet = ∅ := by
    simp [Pcf.DeltaDynamics.postcriticalSet, Pcf.DeltaDynamics.branch, hcrit]
  unfold Pcf.DeltaDynamics.IsPCF
  rw [hpost]
  exact Set.finite_empty

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

instance X_isLocallyNoetherian : IsLocallyNoetherian (X k i hi) :=
  LocallyOfFiniteType.isLocallyNoetherian (sX k i hi)

instance X_isNoetherian : IsNoetherian (X k i hi) where

theorem fX_isGenericallySeparable : Pcf.IsGenericallySeparable (fX k i hi) :=
  Pcf.isGenericallySeparable_of_isPrimeToPMonodromyMap 3 _ (fX_isPrimeToThreeMonodromy k i hi)

instance normalizationLift_etale : Etale (Pcf.schemeGlobalNormalizationLift (fX k i hi)) := by
  rw [normalizationLift_eq]; infer_instance

/-- **`f` is PCF in the sense of `def:pcf`** (`Pcf.IsSeparableNormalizedPCF`).

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem fX_isSeparableNormalizedPCF : Pcf.IsSeparableNormalizedPCF k (sX k i hi) (fX k i hi) := by
  rw [Pcf.isSeparableNormalizedPCF_iff_downstairs, Pcf.isWeightedNormalizedPCFDownstairs_iff]
  exact ⟨fX_isGenericallySeparable k i hi, deltaDynamics_isPCF_of_etale _⟩

#print axioms deltaDynamics_isPCF_of_etale
#print axioms fX_isSeparableNormalizedPCF

end Pcf.Examples.PaperP.MonodromyLossGlobal
