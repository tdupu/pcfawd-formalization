/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalX
public import Pcf.Examples.PaperP.MonodromyLossReturnScheme

/-!
# Descent of `F` to the pinched variety `X` (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss`: "The map `F` descends to a finite map `f` of the
resulting nonnormal variety `X`. [...] The two pinched divisors form a `2`-cycle, and the return on
the first is `g(y) = -i (y⁴ + 1)/y³`. Indeed, `φ² = 2ι` and the duplication formula gives
`y(2P) = -(y(P)⁴ + 1)/y(P)³`."

By the pushout property `isPushoutX`, a map `f : X ⟶ X` with `ν ≫ f = F ≫ ν` exists iff
`F ≫ ν` is constant on the fibres of the pinching. On the first copy of `E`, `F` maps
`E × {0}` to `E × {∞}` by `φ`, and `E × {∞}` is pinched along `y ∘ φ`; so the compatibility on
`E × {0}` (pinched along `y`) needs a map `g : ℙ¹ ⟶ ℙ¹` with `y ≫ g = φ ≫ φ ≫ y`, i.e.
`y(φ² P) = g(y(P))`. This is exactly the identity the source derives from `φ² = 2ι` and the
duplication formula. On the second copy the compatibility is automatic (`g = id`).

This file takes the scheme-level identity `y ≫ g = φ² ≫ y` as the hypothesis `hg` (it is not yet
formalized at scheme level; see the evidence file) and derives:

* **`f`**, **`nu_f : ν ≫ f = F ≫ ν`** (and uniqueness `f_unique`);
* **`o0_f`**, **`oInf_f`**: `f` maps the first pinched divisor to the second by `g`, and the
  second to the first by the identity of `ℙ¹` — the two pinched divisors form a `2`-cycle;
* **`o0_f_f`**: the return of `f²` on the first pinched divisor is `g`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductSlices Pcf.Examples.PaperP.TwoChartPinch
open Pcf.Examples.PaperP.MonodromyLossInf Pcf.Examples.PaperP.PinchedPushoutGlobal
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

local notation "P1" => Proj (grading k)

/-- The return `g : ℙ¹ ⟶ ℙ¹`, `g(y) = -i (y⁴ + 1)/y³`. -/
noncomputable abbrev gMap : P1 ⟶ P1 := MonodromyLossReturn.schemeMap k i hi

/-- The map on `ℙ¹ ⨿ ℙ¹` covered by `F`: the first line goes to the second by `g`, the second to
the first by the identity. -/
noncomputable def oF : P1 ⨿ P1 ⟶ X k i hi :=
  coprod.desc (gMap k i hi ≫ coprod.inr ≫ oX k i hi) (coprod.inl ≫ oX k i hi)

variable {k i hi}

/-- **Compatibility of `F` with the pinching**, given `y(φ² P) = g(y(P))`. -/
theorem descent_compat (hg : yMap k ≫ gMap k i hi = phi k i hi ≫ phi k i hi ≫ yMap k) :
    iZ k ≫ bigF k i hi ≫ nu k i hi = jZ k i hi ≫ oF k i hi := by
  have w := w k i hi
  refine coprod.hom_ext ?_ ?_
  · rw [iZ, coprod.inl_desc_assoc, ← Category.assoc, slice0_bigF, Category.assoc,
      show sliceInf k = coprod.inr ≫ iZ k from (coprod.inr_desc _ _).symm, Category.assoc, w,
      jZ, coprod.inr_map_assoc, coprod.inl_map_assoc, oF, coprod.inl_desc,
      ← Category.assoc (yMap k), hg]
    simp only [Category.assoc]
  · rw [iZ, coprod.inr_desc_assoc, ← Category.assoc, sliceInf_bigF, Category.assoc,
      show slice0 k = coprod.inl ≫ iZ k from (coprod.inl_desc _ _).symm, Category.assoc, w,
      jZ, coprod.inl_map_assoc, coprod.inr_map_assoc, oF, coprod.inr_desc, Category.assoc]

variable (hg : yMap k ≫ gMap k i hi = phi k i hi ≫ phi k i hi ≫ yMap k)

/-- **`F` descends: `f : X ⟶ X`.** -/
noncomputable def f : X k i hi ⟶ X k i hi :=
  (isPushoutX k i hi).desc (bigF k i hi ≫ nu k i hi) (oF k i hi) (descent_compat hg)

/-- **`ν ∘ F = f ∘ ν`.** -/
@[reassoc] theorem nu_f : nu k i hi ≫ f hg = bigF k i hi ≫ nu k i hi :=
  (isPushoutX k i hi).inl_desc _ _ _

@[reassoc] theorem oX_f : oX k i hi ≫ f hg = oF k i hi :=
  (isPushoutX k i hi).inr_desc _ _ _

/-- `f` is the only map with `ν ∘ F = f ∘ ν` (`ν` is an epimorphism). -/
theorem f_unique (f' : X k i hi ⟶ X k i hi) (h : nu k i hi ≫ f' = bigF k i hi ≫ nu k i hi) :
    f' = f hg := by
  have : Epi (nu k i hi) := epi_of_surjective_of_isSchemeTheoreticallyDominant _
  rw [← cancel_epi (nu k i hi), h, nu_f]

/-- **The first pinched divisor goes to the second, by `g`.** -/
@[reassoc] theorem o0_f : (D0 k).o ≫ j0 k i hi ≫ f hg =
    gMap k i hi ≫ (infData k i hi).o ≫ jInf k i hi := by
  have h1 : (D0 k).o ≫ j0 k i hi = coprod.inl ≫ oX k i hi := (coprod.inl_desc _ _).symm
  have h2 : (infData k i hi).o ≫ jInf k i hi = coprod.inr ≫ oX k i hi :=
    (coprod.inr_desc _ _).symm
  rw [← Category.assoc, h1, Category.assoc, oX_f, oF, coprod.inl_desc, h2]

/-- **The second pinched divisor goes back to the first, by the identity of `ℙ¹`.** -/
@[reassoc] theorem oInf_f : (infData k i hi).o ≫ jInf k i hi ≫ f hg = (D0 k).o ≫ j0 k i hi := by
  have h1 : (D0 k).o ≫ j0 k i hi = coprod.inl ≫ oX k i hi := (coprod.inl_desc _ _).symm
  have h2 : (infData k i hi).o ≫ jInf k i hi = coprod.inr ≫ oX k i hi :=
    (coprod.inr_desc _ _).symm
  rw [← Category.assoc, h2, Category.assoc, oX_f, oF, coprod.inr_desc, h1]

/-- **The return on the first pinched divisor is `g`.** -/
theorem o0_f_f : (D0 k).o ≫ j0 k i hi ≫ f hg ≫ f hg = gMap k i hi ≫ (D0 k).o ≫ j0 k i hi := by
  rw [o0_f_assoc, oInf_f]

#print axioms f
#print axioms nu_f
#print axioms o0_f_f

end Pcf.Examples.PaperP.MonodromyLossGlobal
