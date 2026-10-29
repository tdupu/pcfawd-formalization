/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalBirational
public import Pcf.Examples.PaperP.MonodromyLossCurveRegular
public import Pcf.Bounding.PaperPTowerRestrict
public import Pcf.Bounding.AllCodimBlowupGlobalNormalizedBranch
public import Pcf.Stacks.Common.RegularNormal

/-!
# `E ×ₖ ℙ¹` is normal (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): `F` lives on the normal variety
`E ×ₖ ℙ¹`, which is the normalization of `X`.

* `isIntegrallyClosed_of_spec_stalks`, `stalk_isIntegrallyClosed_of_isOpenImmersion` (general);
* `A_isIntegrallyClosed`, `B_isIntegrallyClosed`: the chart rings of `E` are normal (their local
  rings are local rings of `E`, which are regular, `isRegularLocalRing_stalk`);
* `D0_EA_stalk_isIntegrallyClosed`: the local rings of `E × 𝔸¹` (charts `A[z]`, `B[z]`);
* **`EP1_isNormalScheme`**: `E ×ₖ ℙ¹` is normal (every point lies in one of the two charts
  `E × 𝔸¹ → E ×ₖ ℙ¹`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

universe u

set_option linter.style.haveILetI false

/-- A domain all of whose local rings (stalks of `Spec R`) are integrally closed is integrally
closed. -/
theorem isIntegrallyClosed_of_spec_stalks (R : Type u) [CommRing R] [IsDomain R]
    (h : ∀ p : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk p)) :
    IsIntegrallyClosed R := by
  haveI := Pcf.isNormalScheme_of_stalk_integrallyClosed (Spec (.of R)) h
  haveI : IsIntegrallyClosed Γ(Spec (.of R), ⊤) :=
    Pcf.IsNormalScheme.component_integrallyClosed ⟨⊤, isAffineOpen_top _⟩
  exact IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv

/-- Normality of local rings transfers along open immersions. -/
theorem stalk_isIntegrallyClosed_of_isOpenImmersion {U Y : Scheme.{u}} (f : U ⟶ Y)
    [IsOpenImmersion f] (x : U) (h : IsIntegrallyClosed (Y.presheaf.stalk (f x))) :
    IsIntegrallyClosed (U.presheaf.stalk x) :=
  IsIntegrallyClosed.of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- Normality of local rings transfers along open immersions (converse direction). -/
theorem stalk_isIntegrallyClosed_of_isOpenImmersion' {U Y : Scheme.{u}} (f : U ⟶ Y)
    [IsOpenImmersion f] (x : U) (h : IsIntegrallyClosed (U.presheaf.stalk x)) :
    IsIntegrallyClosed (Y.presheaf.stalk (f x)) :=
  IsIntegrallyClosed.of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductIntegral
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossPinchGlue

set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

theorem E_stalk_isIntegrallyClosed (x : E k) : IsIntegrallyClosed ((E k).presheaf.stalk x) := by
  haveI := isRegularLocalRing_stalk k x
  exact Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing _

instance A_isIntegrallyClosed : IsIntegrallyClosed (A k) :=
  isIntegrallyClosed_of_spec_stalks _ fun p =>
    stalk_isIntegrallyClosed_of_isOpenImmersion (ιA k) p (E_stalk_isIntegrallyClosed k _)

instance B_isIntegrallyClosed : IsIntegrallyClosed (B k) :=
  isIntegrallyClosed_of_spec_stalks _ fun p =>
    stalk_isIntegrallyClosed_of_isOpenImmersion (ιB k) p (E_stalk_isIntegrallyClosed k _)

theorem D0_EA_stalk_isIntegrallyClosed (z : (D0 k).EA) :
    IsIntegrallyClosed ((D0 k).EA.presheaf.stalk z) := by
  rcases TwoChartGlue.cover (D0 k).q0 (D0 k).q1 z with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · haveI := PaperPTower.isNormalScheme_spec (Polynomial (A k))
    exact stalk_isIntegrallyClosed_of_isOpenImmersion' _ a
      (Pcf.Bounding.AllCodimBlowup.isNormalScheme_stalk_integrallyClosed a)
  · haveI := PaperPTower.isNormalScheme_spec (Polynomial (B k))
    exact stalk_isIntegrallyClosed_of_isOpenImmersion' _ b
      (Pcf.Bounding.AllCodimBlowup.isNormalScheme_stalk_integrallyClosed b)

/-- The second chart `E × 𝔸¹ → E ×ₖ ℙ¹` (at infinity), through `D0.EA`. -/
noncomputable def c0' : (D0 k).EA ⟶ EP1 k := (theta0 k).hom ≫ chartEP1 k eU

instance c0'_isOpenImmersion : IsOpenImmersion (c0' k) := by unfold c0'; infer_instance

/-- **`E ×ₖ ℙ¹` is normal.** -/
instance EP1_isNormalScheme : Pcf.IsNormalScheme (EP1 k) := by
  apply Pcf.isNormalScheme_of_stalk_integrallyClosed
  intro x
  have hcov : x ∈ Set.range (c0 k) ∨ x ∈ Set.range (c0' k) := by
    rw [c0, c0', range_iso_comp, range_iso_comp, range_chartEP1, range_chartEP1]
    exact chartP1_cover k _
  rcases hcov with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact stalk_isIntegrallyClosed_of_isOpenImmersion' (c0 k) z (D0_EA_stalk_isIntegrallyClosed k z)
  · exact stalk_isIntegrallyClosed_of_isOpenImmersion' (c0' k) z
      (D0_EA_stalk_isIntegrallyClosed k z)

#print axioms EP1_isNormalScheme

end Pcf.Examples.PaperP.MonodromyLossGlobal
