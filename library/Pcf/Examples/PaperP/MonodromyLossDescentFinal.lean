/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalDescent
public import Pcf.Examples.PaperP.MonodromyLossReturnIdentity

/-!
# The unconditional descent of `F` to `X` (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss`: "The map `F` descends to a finite map `f` of the
resulting nonnormal variety `X`. [...] The two pinched divisors form a `2`-cycle, and the return on
the first is `g(y) = -i (y⁴ + 1)/y³`."

`MonodromyLossGlobalDescent` builds the descent under the hypothesis `hg : y ≫ g = φ ≫ φ ≫ y`.
That hypothesis is the scheme identity `MonodromyLossCurve.yMap_comp_schemeMap`
(`MonodromyLossReturnIdentity`), so the descent is unconditional:

* **`hg_true`**: `y ≫ g = φ ≫ φ ≫ y`;
* **`fX : X ⟶ X`**, **`nu_fX : ν ≫ f = F ≫ ν`**, `fX_unique`;
* **`o0_fX`**, **`oInf_fX`**: the two pinched divisors form a `2`-cycle (by `g`, then by the
  identity of `ℙ¹`);
* **`o0_fX_fX`**: the return of `f²` on the first pinched divisor is `g`.

Finiteness of `f` is not proved here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossInf Pcf.Examples.PaperP.TwoChartPinch

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- **The return identity** `y ∘ φ² = g ∘ y`, the hypothesis of the descent. -/
theorem hg_true : yMap k ≫ gMap k i hi = phi k i hi ≫ phi k i hi ≫ yMap k :=
  yMap_comp_schemeMap k i hi

/-- **`F` descends to `f : X ⟶ X`**, unconditionally. -/
noncomputable def fX : X k i hi ⟶ X k i hi := f (hg_true k i hi)

/-- **`ν ∘ F = f ∘ ν`.** -/
@[reassoc] theorem nu_fX : nu k i hi ≫ fX k i hi = bigF k i hi ≫ nu k i hi :=
  nu_f (hg_true k i hi)

/-- `f` is the unique map with `ν ∘ F = f ∘ ν`. -/
theorem fX_unique (f' : X k i hi ⟶ X k i hi) (h : nu k i hi ≫ f' = bigF k i hi ≫ nu k i hi) :
    f' = fX k i hi :=
  f_unique (hg_true k i hi) f' h

/-- **The first pinched divisor goes to the second, by `g`.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
@[reassoc] theorem o0_fX : (D0 k).o ≫ j0 k i hi ≫ fX k i hi =
    gMap k i hi ≫ (infData k i hi).o ≫ jInf k i hi :=
  o0_f (hg_true k i hi)

/-- **The second pinched divisor goes back to the first, by the identity of `ℙ¹`.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
@[reassoc] theorem oInf_fX : (infData k i hi).o ≫ jInf k i hi ≫ fX k i hi =
    (D0 k).o ≫ j0 k i hi :=
  oInf_f (hg_true k i hi)

/-- **The return on the first pinched divisor is `g(y) = -i (y⁴ + 1)/y³`.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem o0_fX_fX : (D0 k).o ≫ j0 k i hi ≫ fX k i hi ≫ fX k i hi =
    gMap k i hi ≫ (D0 k).o ≫ j0 k i hi :=
  o0_f_f (hg_true k i hi)

#print axioms hg_true
#print axioms fX
#print axioms nu_fX
#print axioms fX_unique
#print axioms o0_fX
#print axioms oInf_fX
#print axioms o0_fX_fX

end Pcf.Examples.PaperP.MonodromyLossGlobal
