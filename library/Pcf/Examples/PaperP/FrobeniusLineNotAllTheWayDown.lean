/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineInseparableReturn
public import Pcf.Bounding.TheoremADivisors
public import Pcf.Bounding.SchemeGenericSeparabilityMap

/-!
# The Frobenius-line map is not PCF all the way down

The canonical reduced closure used by the paper-facing recursion is identified
with the explicit affine line. Its actual return is inseparable. Already the
first divisor-recursion step therefore fails, despite ordinary ambient PCF.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

local instance lineClosed : IsClosedImmersion (lineEmbedding k) :=
  lineEmbedding_isClosedImmersion k

private theorem lineEmbedding_ker_radical :
    (lineEmbedding k).ker.radical = (lineEmbedding k).ker := by
  ext U : 2
  simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  apply le_antisymm
  · intro r hr
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hr
    change (lineEmbedding k).app U r = 0
    apply IsReduced.eq_zero
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact hn
  · exact Ideal.le_radical

/-- The explicit line and the canonical reduced divisor have the same ideal sheaf. -/
theorem lineEmbedding_ker_eq_pointClosure :
    (lineEmbedding k).ker = Pcf.pointClosureIdealSheaf (linePoint k) := by
  rw [← lineEmbedding_ker_radical k,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker, lineEmbedding_range]
  change closure (PrimeSpectrum.zeroLocus (lineIdeal k : Set (Plane k))) =
    closure {linePoint k}
  rw [(PrimeSpectrum.isClosed_zeroLocus _).closure_eq, PrimeSpectrum.closure_singleton]
  rfl

noncomputable def canonicalLineToExplicit :
    (Pcf.pointClosureIdealSheaf (linePoint k)).subscheme ⟶ Spec (.of (Polynomial k)) := by
  haveI : IsClosedImmersion (lineEmbedding k) := lineEmbedding_isClosedImmersion k
  exact IsClosedImmersion.lift (lineEmbedding k)
    (Pcf.pointClosureIdealSheaf (linePoint k)).subschemeι (by
      rw [Scheme.IdealSheafData.ker_subschemeι, lineEmbedding_ker_eq_pointClosure])

instance canonicalLineToExplicit_isIso : IsIso (canonicalLineToExplicit k) := by
  haveI : IsClosedImmersion (lineEmbedding k) := lineEmbedding_isClosedImmersion k
  apply IsClosedImmersion.isIso_lift
  rw [Scheme.IdealSheafData.ker_subschemeι, lineEmbedding_ker_eq_pointClosure]

@[reassoc (attr := simp)] theorem canonicalLineToExplicit_embedding :
    canonicalLineToExplicit k ≫ lineEmbedding k =
      (Pcf.pointClosureIdealSheaf (linePoint k)).subschemeι := by
  exact IsClosedImmersion.lift_fac ..

local instance noAllFinite : IsFinite (schemeMap k p) :=
  schemeMap_finite k p (Fact.out : p.Prime).two_le
local instance noAllSurjective : Surjective (schemeMap k p) :=
  schemeMap_surjective k p (Fact.out : p.Prime).two_le
local instance noAllLineFinite : IsFinite (lineSchemeMap k p) :=
  lineSchemeMap_finite k p (Fact.out : p.Prime).two_le
local instance noAllLineSurjective : Surjective (lineSchemeMap k p) :=
  lineSchemeMap_surjective k p (Fact.out : p.Prime).two_le

/-- The canonical divisor return used by the recursion is inseparable.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem canonicalLineReturn_not_isGenericallySeparable :
    ¬ Pcf.IsGenericallySeparableSchemeMap
      (Pcf.pointClosureReturnMap (schemeMap k p) (linePoint k) (schemeMap_linePoint k p)) := by
  intro hsep
  apply lineSchemeMap_not_isGenericallySeparable k p
  apply Pcf.isGenericallySeparable_of_finite_commuting_square
    (lineSchemeMap k p)
    (Pcf.pointClosureReturnMap (schemeMap k p) (linePoint k) (schemeMap_linePoint k p))
    (canonicalLineToExplicit k) _ hsep
  rw [← cancel_mono (lineEmbedding k), Category.assoc, canonicalLineToExplicit_embedding,
    Pcf.pointClosureReturnMap, Pcf.pointClosureSubschemeMap_subschemeι,
    Category.assoc, ← restriction_scheme_square, canonicalLineToExplicit_embedding_assoc]

set_option maxHeartbeats 1000000 in
-- Reducing the dependent recursive return type to the fixed line uses extra heartbeats.
/-- The actual map fails the paper's PCF-all-the-way-down divisor predicate.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_not_isPCFAllDivisors :
    ¬ Pcf.IsPCFAllDivisors k (planeStructure k) (schemeMap k p) := by
  intro h
  have h₁ := h 1
  change Pcf.IsSeparableNormalizedPCF k (planeStructure k) (schemeMap k p) ∧ _ at h₁
  have hperiodic : Pcf.schemePointIterate (schemeMap k p) (0 + 1) (lineDivisor k).1 =
      Pcf.schemePointIterate (schemeMap k p) 0 (lineDivisor k).1 := by
    simpa [Pcf.schemePointIterate, lineDivisor] using schemeMap_linePoint k p
  have hreturn := h₁.2 (lineDivisor k) 0 1 le_rfl hperiodic
  change Pcf.IsSeparableNormalizedPCF _ _ _ at hreturn
  obtain ⟨hsep, _⟩ := hreturn
  apply canonicalLineReturn_not_isGenericallySeparable k p
  change Pcf.IsGenericallySeparable
    (Pcf.pointClosureReturnMap (schemeMap k p) (linePoint k) (schemeMap_linePoint k p)) at hsep
  exact hsep

#print axioms lineEmbedding_ker_eq_pointClosure
#print axioms canonicalLineToExplicit_isIso
#print axioms canonicalLineReturn_not_isGenericallySeparable
#print axioms schemeMap_not_isPCFAllDivisors

end Pcf.Examples.PaperP.FrobeniusLine
