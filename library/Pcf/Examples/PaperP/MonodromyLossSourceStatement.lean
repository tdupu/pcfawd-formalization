/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalSeparablePCF
public import Pcf.Examples.PaperP.MonodromyLossReturnStatement

/-!
# `ex:monodromy-loss`, sentence by sentence

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868), as one bundled statement
(`monodromyLoss_source_statement`):

1. `E : y² = x³ - x` over `k` (char 3, `i² = -1`) is separated and of finite type over `k`;
   `φ : E → E` is finite and étale of degree 2;
2. `F = (φ, 1/z)` on `E ×ₖ ℙ¹` is finite and étale of degree 2;
3. `X` (pinch `E × {0}` along `y` and `E × {∞}` along `y ∘ φ`) is the pushout of
   `E ×ₖ ℙ¹ ← E ⨿ E → ℙ¹ ⨿ ℙ¹`; it is an integral, separated, finite-type, nonnormal `k`-scheme;
4. `ν : E ×ₖ ℙ¹ → X` is finite, and `X̃ ≅ E ×ₖ ℙ¹` over `X`;
5. `F` descends to `f : X → X` (`ν ∘ F = f ∘ ν`); `f` is finite, its normalization lift is `F`;
6. `f` is PCF (`def:pcf`, `IsSeparableNormalizedPCF`) with prime-to-3 monodromy;
7. the pinched divisors form a 2-cycle (by `g`, then the identity), with return `g` on the first;
8. `g` is the return map of `MonodromyLossReturn.return_statement` (ramified at `0`, not
   prime-to-3, PCF);
9. `F²|_{E × {0}}` is `φ²`, finite of degree 4 with prime-to-3 monodromy.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductSlices
open BasilicaProjectiveScheme (grading)

set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- **`ex:monodromy-loss`, bundled.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem monodromyLoss_source_statement :
    -- (1) the curve and `φ`
    (LocallyOfFiniteType (toSpec k) ∧ QuasiCompact (toSpec k) ∧ IsSeparated (toSpec k)) ∧
    (IsFinite (phi k i hi) ∧ Etale (phi k i hi) ∧
      (letI := ((phi k i hi).stalkMap (genericPoint (E k))).hom.toAlgebra;
        Module.finrank ((E k).presheaf.stalk (phi k i hi (genericPoint (E k))))
          ((E k).presheaf.stalk (genericPoint (E k))) = 2)) ∧
    -- (2) `F`
    (IsFinite (bigF k i hi) ∧ Etale (bigF k i hi) ∧
      (letI := ((bigF k i hi).stalkMap (genericPoint (EP1 k))).hom.toAlgebra;
        Module.finrank ((EP1 k).presheaf.stalk (bigF k i hi (genericPoint (EP1 k))))
          ((EP1 k).presheaf.stalk (genericPoint (EP1 k))) = 2)) ∧
    -- (3) the pinched `X`
    IsPushout (iZ k) (jZ k i hi) (nu k i hi) (oX k i hi) ∧
    (IsIntegral (X k i hi) ∧ LocallyOfFiniteType (sX k i hi) ∧ QuasiCompact (sX k i hi) ∧
      IsSeparated (sX k i hi) ∧ ¬ Pcf.IsNormalScheme (X k i hi)) ∧
    -- (4) `ν` is the normalization
    IsFinite (nu k i hi) ∧
    (normalizationIso k i hi).hom ≫ nu k i hi = Pcf.Palomar.normalizationMap (X k i hi) ∧
    -- (5) the descent `f`, finite, with normalization `F`
    nu k i hi ≫ fX k i hi = bigF k i hi ≫ nu k i hi ∧ IsFinite (fX k i hi) ∧
    Pcf.schemeGlobalNormalizationLift (fX k i hi) =
      (normalizationIso k i hi).hom ≫ bigF k i hi ≫ (normalizationIso k i hi).inv ∧
    -- (6) PCF with prime-to-3 monodromy
    Pcf.IsSeparableNormalizedPCF k (sX k i hi) (fX k i hi) ∧
    Pcf.Palomar.IsNormalizedPCF (fX k i hi) ∧
    Pcf.IsPrimeToPMonodromyMap 3 (fX k i hi) ∧
    -- (7) the 2-cycle of pinched divisors and the return
    (D0 k).o ≫ j0 k i hi ≫ fX k i hi = gMap k i hi ≫ (MonodromyLossInf.infData k i hi).o ≫
      jInf k i hi ∧
    (MonodromyLossInf.infData k i hi).o ≫ jInf k i hi ≫ fX k i hi = (D0 k).o ≫ j0 k i hi ∧
    (D0 k).o ≫ j0 k i hi ≫ fX k i hi ≫ fX k i hi = gMap k i hi ≫ (D0 k).o ≫ j0 k i hi ∧
    -- (8) the return `g`
    (IsFinite (gMap k i hi) ∧ Surjective (gMap k i hi) ∧
      Pcf.Palomar.ramificationIndexAt (gMap k i hi) (BasilicaProjectiveScheme.zero k) = 3 ∧
      ¬ Pcf.IsPrimeToPMonodromyMap 3 (gMap k i hi) ∧
      Pcf.IsSeparableNormalizedPCF k (BasilicaProjectiveScheme.structureMap k) (gMap k i hi) ∧
      Pcf.Palomar.IsPCF (gMap k i hi)) ∧
    -- (9) `F²|_{E×{0}}`
    (IsPullback (phiSq k i hi) (slice0 k) (slice0 k) (bigF k i hi ≫ bigF k i hi) ∧
      IsFinite (phiSq k i hi) ∧
      (letI := ((phiSq k i hi).stalkMap (genericPoint (E k))).hom.toAlgebra;
        Module.finrank ((E k).presheaf.stalk (phiSq k i hi (genericPoint (E k))))
          ((E k).presheaf.stalk (genericPoint (E k))) = 4) ∧
      Pcf.IsPrimeToPMonodromyMap 3 (phiSq k i hi)) := by
  obtain ⟨g1, g2, -, g4, g5, -, -, -, -, -, g11, g12⟩ :=
    MonodromyLossReturn.return_statement k hi
  obtain ⟨-, r2, r3, r4, r5⟩ := bigFSq_restrict_zero k i hi
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, phi_genericDegree k i hi⟩,
    ⟨inferInstance, inferInstance, MonodromyLossProductDegree.bigF_genericDegree k i hi⟩,
    isPushoutX k i hi,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, X_not_isNormalScheme k i hi⟩,
    inferInstance, normalizationIso_hom_nu k i hi,
    nu_fX k i hi, inferInstance, normalizationLift_eq k i hi,
    fX_isSeparableNormalizedPCF k i hi, fX_isNormalizedPCF k i hi,
    fX_isPrimeToThreeMonodromy k i hi,
    o0_fX k i hi, oInf_fX k i hi, o0_fX_fX k i hi,
    ⟨g1, g2, g4, g5, g11, g12⟩,
    ⟨r2, r3, r4, r5⟩⟩

#print axioms monodromyLoss_source_statement

end Pcf.Examples.PaperP.MonodromyLossGlobal
