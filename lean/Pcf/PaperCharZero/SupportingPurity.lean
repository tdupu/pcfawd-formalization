/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI

/-!
# Source-facing scheme purity

Theorem `thm:purity` in `paper.tex`, with the source's pointwise quasi-finiteness
and unramifiedness hypotheses. No finite-type hypothesis on the entire morphism
is added: the Stacks pointwise quasi-finiteness definition already includes a
finite-type affine neighborhood. The conclusion is an actual étale neighborhood.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace Pcf.PaperCharZero

/-- `paper.tex`, `thm:purity`: Zariski--Nagata purity for a morphism of locally
Noetherian schemes, with exactly the stated local hypotheses. This is the
proved scheme-level Stacks `0BMB` theorem with its conclusion transported to
Mathlib's `Etale` predicate on an open neighborhood. It holds in every
characteristic and does not require global finite type, normality, or regularity.

Manuscript: `thm:purity` (Theorem 6.1). -/
theorem zariski_nagata_purity
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (h : X ⟶ Y) (x : X)
    (hnormal : Stacks.IsStacksNormalRing (X.presheaf.stalk x))
    (hregular : IsRegularLocalRing (Y.presheaf.stalk (h x)))
    (hquasifinite : Stacks.IsStacksQuasiFiniteAt h x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (h x)))
    (hpositive : 1 ≤ ringKrullDim (Y.presheaf.stalk (h x)))
    (hunramified : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      Stacks.IsStacksUnramifiedAt h x') :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ h) := by
  apply (Stacks.isStacksEtaleAt_iff_exists_etale (f := h) x).mp
  exact Stacks.isStacksEtaleAt_of_zariskiNagataPurity h x hnormal hregular
    hquasifinite hdim (hdim.symm ▸ hpositive) hunramified

end Pcf.PaperCharZero
